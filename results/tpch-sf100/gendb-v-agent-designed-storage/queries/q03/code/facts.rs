//! What every database bound to the parts gives about the model (`model`): part kinds for the extent reads, the
//! layout and decoded values (`facts` represents lineitem and orders through row maps, `custpart` represents
//! customer in canonical order), the declared primary keys of orders and customer at the part level, and the
//! co-clustering of lineitem with orders. Per table: one lemma unpacks only the columns read (`*_cols`), one states a
//! row (`*_row`), one collects the table's facts; `lemma_model` combines them.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::{db_wf, value_in_column};
use crate::spec::numeric::pow10;
use crate::spec::constraints::{constraints_hold, key_of};
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::link::query::{proj, proj_all};
use crate::link::source::{rows_in_columns, lemma_proj_all_index};
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::bridge::equality::lemma_row_not_distinct_refl;
use crate::stores::facts::interface as fi;
use crate::stores::custpart::interface as ci;
use crate::stores::facts::declaration as fd;
use crate::stores::li_okruns::interface as lr;
use crate::stores::li_okruns::declaration as lrd;
use crate::stores::custpart::declaration as cd;
use fi::common::colfmt as ff;
use ci::common::colfmt as cf;
use super::model::*;

verus! {

/// Kinds and lengths of the parts the query reads (what the extent reads require).
pub open spec fn kinds_ok(sv: StoresView) -> bool {
    let f = fparts(sv);
    let c = sv.custpart;
    &&& sv.li_okruns.len() == 76 && sv.li_okruns[R_STARTS as int] is U32
    &&& f.len() == 75
    &&& f[F_L_LAYOUT as int] is U64 && pv_u64(f[F_L_LAYOUT as int]).len() == 2
    &&& f[F_L_KEY_C as int] is U32 && f[F_L_KEY_B as int] is I64
    &&& f[F_L_PRICE_C as int] is U32 && f[F_L_PRICE_B as int] is I64
    &&& f[F_L_DISC_C as int] is U8 && f[F_L_DISC_B as int] is I64
    &&& f[F_L_SHIP_C as int] is U16 && f[F_L_SHIP_B as int] is I64 && f[F_L_SHIP_Z as int] is I64
    &&& f[F_O_LAYOUT as int] is U64 && pv_u64(f[F_O_LAYOUT as int]).len() == 2
    &&& f[F_O_KEY_C as int] is U32 && f[F_O_KEY_B as int] is I64
    &&& f[F_O_CUST_C as int] is U32 && f[F_O_CUST_B as int] is I64
    &&& f[F_O_DATE_C as int] is U16 && f[F_O_DATE_B as int] is I64
    &&& f[F_O_SP_C as int] is U8 && f[F_O_SP_B as int] is I64
    &&& f[F_O_IDX_C as int] is U32 && f[F_O_IDX_B as int] is U64
    &&& f[F_O_IDX_KIND as int] is U64 && pv_u64(f[F_O_IDX_KIND as int]).len() == 1
    &&& f[F_CLUSTER as int] is U64 && pv_u64(f[F_CLUSTER as int]).len() == 1
    &&& c.len() > 20
    &&& c[C_LAYOUT as int] is U64 && pv_u64(c[C_LAYOUT as int]).len() == 2
    &&& c[C_KEY_C as int] is U32 && c[C_KEY_B as int] is I64
    &&& c[C_SEG_C as int] is U8 && c[C_SEG_B as int] is U64
    &&& c[C_DICT_OFF as int] is U64 && c[C_DICT_BYTES as int] is U8
    &&& c[C_IDX_KIND as int] is U64 && pv_u64(c[C_IDX_KIND as int]).len() == 1
}

// ------------------------------------------------------------------------------------------------ groups

/// Uniform groups: the group count bounds the rows.
proof fn lemma_fgroups(p: PartView, n: int, bs: int, nb: int)
    requires ff::groups_part_ok(p, n, bs), nb == ff::u64s(p).len() - 1,
    ensures nb >= 0, nb * bs >= n, nb > 0 ==> (nb - 1) * bs < n,
{
    ff::lemma_uniform_groups(p, n, bs);
    ff::lemma_nblocks(n, bs);
}

proof fn lemma_cgroups(p: PartView, n: int, bs: int, nb: int)
    requires cf::groups_part_ok(p, n, bs), nb == cf::u64s(p).len() - 1,
    ensures nb >= 0, nb * bs >= n, nb > 0 ==> (nb - 1) * bs < n,
{
    cf::lemma_uniform_groups(p, n, bs);
    cf::lemma_nblocks(n, bs);
}

// ------------------------------------------------------------------------------------------------ lineitem

/// The lineitem columns this query reads, over the stored rows.
pub open spec fn li_cols(tp: Seq<PartView>, rows: Seq<Row>) -> bool {
    &&& tp[4] is U32 && ff::int_col_at(tp, 1, 4, 5, rows, 0)
    &&& tp[14] is U32 && ff::num_col_at(tp, 1, 14, 15, rows, 5, 2)
    &&& tp[16] is U8 && ff::num_col_at(tp, 1, 16, 17, rows, 6, 2)
    &&& tp[28] is U16 && ff::date_col_at(tp, 1, 28, 29, rows, 10)
    &&& ff::zone_at(tp, 1, 28, 29, 30)
}

proof fn lemma_li_cols(tp: Seq<PartView>, rel: Seq<Row>)
    requires fi::lineitem_ok(tp, rel),
    ensures
        li_cols(tp, fi::lineitem_rows(tp, rel)),
        fi::table_layout_ok(tp, rel.len() as int),
        ff::perm_col_at(tp, 1, 2, 3, rel.len() as int),
{
}

/// The lineitem model fields are the lineitem parts `tp`.
pub open spec fn li_fields(m: M, tp: Seq<PartView>) -> bool {
    &&& m.l_key_c == pv_u32(tp[4]) && m.l_key_b == pv_i64(tp[5])
    &&& m.l_price_c == pv_u32(tp[14]) && m.l_price_b == pv_i64(tp[15])
    &&& m.l_disc_c == pv_u8(tp[16]) && m.l_disc_b == pv_i64(tp[17])
    &&& m.l_ship_c == pv_u16(tp[28]) && m.l_ship_b == pv_i64(tp[29]) && m.l_ship_z == pv_i64(tp[30])
}

proof fn lemma_li_row(tp: Seq<PartView>, rel: Seq<Row>, t: Seq<Row>, m: M, j: int)
    requires
        li_cols(tp, fi::lineitem_rows(tp, rel)),
        ff::groups_part_ok(tp[1], rel.len() as int, m.l_bs),
        m.l_n == rel.len(),
        m.l_map == fi::lineitem_map(tp, m.l_n),
        ff::is_perm(m.l_map, m.l_n),
        li_fields(m, tp),
        rel == proj_all(t, fd::stored_cols_t0()),
        rows_in_columns(rel, fd::stored_columns_t0()),
        0 <= j < m.l_n,
    ensures
        proj(t[m.l_map[j]], lcols()) == lrow(m, j),
        fi::lineitem_rows(tp, rel)[j][0] == Val::Int(lkey(m, j)),
        in_i64(lkey(m, j)),
        -pow10(15) < lprice(m, j) < pow10(15),
        -pow10(15) < ldisc(m, j) < pow10(15),
        in_i64(lship(m, j)),
        lship(m, j) <= m.l_ship_z[j / m.l_bs],
{
    let n = m.l_n;
    let bs = m.l_bs;
    let rows = fi::lineitem_rows(tp, rel);
    let gs = ff::gs_at(tp, 1);
    let i = m.l_map[j];
    assert(0 <= i < n);
    lemma_proj_all_index(t, fd::stored_cols_t0());
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[5], tp[4], j);
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[15], tp[14], j);
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[17], tp[16], j);
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[29], tp[28], j);
    assert(rows[j] == rel[i]);
    assert(rows[j][0] == Val::Int(lkey(m, j)));
    assert(rows[j][5] == Val::Num { coeff: lprice(m, j), scale: 2 });
    assert(rows[j][6] == Val::Num { coeff: ldisc(m, j), scale: 2 });
    assert(rows[j][10] == Val::Date(lship(m, j)));
    assert(rel[i] == proj(t[i], fd::stored_cols_t0()));
    assert(t[i][0] == rel[i][0]);
    assert(t[i][5] == rel[i][5]);
    assert(t[i][6] == rel[i][6]);
    assert(t[i][10] == rel[i][10]);
    assert(proj(t[i], lcols()) =~= lrow(m, j));
    assert(value_in_column(rel[i][0], fd::stored_columns_t0()[0]));
    assert(value_in_column(rel[i][5], fd::stored_columns_t0()[5]));
    assert(value_in_column(rel[i][6], fd::stored_columns_t0()[6]));
    assert(value_in_column(rel[i][10], fd::stored_columns_t0()[10]));
    assert(ff::in_group(gs, j / bs, j));
    assert(ff::zone_max_ok(gs, tp[29], tp[28], ff::i64s(tp[30])));
}

/// Lineitem facts of the model.
pub open spec fn li_ok(m: M, db: Database) -> bool {
    &&& 1 <= m.l_bs && 0 <= m.l_n && m.l_n + m.l_bs <= u64::MAX
    &&& m.l_nb * m.l_bs >= m.l_n && (m.l_nb > 0 ==> (m.l_nb - 1) * m.l_bs < m.l_n) && m.l_nb >= 0
    &&& m.l_key_c.len() == m.l_n && m.l_key_b.len() == m.l_nb
    &&& m.l_price_c.len() == m.l_n && m.l_price_b.len() == m.l_nb
    &&& m.l_disc_c.len() == m.l_n && m.l_disc_b.len() == m.l_nb
    &&& m.l_ship_c.len() == m.l_n && m.l_ship_b.len() == m.l_nb && m.l_ship_z.len() == m.l_nb
    &&& m.l_n == db.tables[0].len()
    &&& ff::is_perm(m.l_map, m.l_n)
    &&& forall|j: int| 0 <= j < m.l_n ==> #[trigger] proj(db.tables[0][m.l_map[j]], lcols()) == lrow(m, j)
    &&& forall|j: int| 0 <= j < m.l_n ==> {
        &&& in_i64(#[trigger] lkey(m, j))
        &&& -pow10(15) < lprice(m, j) < pow10(15)
        &&& -pow10(15) < ldisc(m, j) < pow10(15)
        &&& in_i64(lship(m, j)) && lship(m, j) <= m.l_ship_z[j / m.l_bs]
    }
}

/// The lineitem stored rows and their key column (for the cluster flag).
pub open spec fn li_keys(sv: StoresView, db: Database) -> bool {
    let lrows = fi::lineitem_rows(fparts(sv).subrange(0, 48), fd::stored_relations(db)[0]);
    &&& lrows.len() == model_of(sv).l_n
    &&& forall|j: int| 0 <= j < model_of(sv).l_n ==> #[trigger] lrows[j][0] == Val::Int(lkey(model_of(sv), j))
}

proof fn lemma_lineitem(sv: StoresView, db: Database)
    requires
        fi::represents(fparts(sv), fd::stored_relations(db)),
        db.schema == schema_spec(),
        db_wf(db),
    ensures
        li_ok(model_of(sv), db),
        li_keys(sv, db),
        fparts(sv)[F_L_LAYOUT as int] is U64 && pv_u64(fparts(sv)[F_L_LAYOUT as int]).len() == 2,
        fparts(sv)[F_L_KEY_C as int] is U32 && fparts(sv)[F_L_KEY_B as int] is I64,
        fparts(sv)[F_L_PRICE_C as int] is U32 && fparts(sv)[F_L_PRICE_B as int] is I64,
        fparts(sv)[F_L_DISC_C as int] is U8 && fparts(sv)[F_L_DISC_B as int] is I64,
        fparts(sv)[F_L_SHIP_C as int] is U16 && fparts(sv)[F_L_SHIP_B as int] is I64 && fparts(sv)[F_L_SHIP_Z as int] is I64,
{
    let m = model_of(sv);
    let f = fparts(sv);
    let rels = fd::stored_relations(db);
    let tp = f.subrange(0, 48);
    let rel = rels[0];
    let t = db.tables[0];
    lemma_li_cols(tp, rel);
    fd::lemma_stored_relations(db);
    fd::lemma_declared_schema();
    let n = rel.len() as int;
    let bs = ff::u64s(tp[0])[1] as int;
    assert(tp[0] == f[0] && tp[1] == f[1]);
    assert(pv_u64(f[0]) == ff::u64s(tp[0]));
    assert(m.l_n == n && m.l_bs == bs);
    assert(tp[4] == f[4] && tp[5] == f[5] && tp[14] == f[14] && tp[15] == f[15] && tp[16] == f[16] && tp[17] == f[17]);
    assert(tp[28] == f[28] && tp[29] == f[29] && tp[30] == f[30]);
    assert(li_fields(m, tp));
    lemma_fgroups(tp[1], n, bs, m.l_nb);
    assert(rel == proj_all(t, fd::stored_cols_t0()));
    assert(db.tables.len() == 8);
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] proj(db.tables[0][m.l_map[j]], lcols()) == lrow(m, j) by {
        lemma_li_row(tp, rel, t, m, j);
    }
    assert forall|j: int| 0 <= j < m.l_n implies {
        &&& in_i64(#[trigger] lkey(m, j))
        &&& -pow10(15) < lprice(m, j) < pow10(15)
        &&& -pow10(15) < ldisc(m, j) < pow10(15)
        &&& in_i64(lship(m, j)) && lship(m, j) <= m.l_ship_z[j / m.l_bs]
    } by {
        lemma_li_row(tp, rel, t, m, j);
    }
    let lrows = fi::lineitem_rows(tp, rel);
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] lrows[j][0] == Val::Int(lkey(m, j)) by {
        lemma_li_row(tp, rel, t, m, j);
    }
}

// ------------------------------------------------------------------------------------------------ orders

pub open spec fn or_cols(tp: Seq<PartView>, rows: Seq<Row>) -> bool {
    &&& tp[4] is U32 && ff::int_col_at(tp, 1, 4, 5, rows, 0)
    &&& tp[6] is U32 && ff::int_col_at(tp, 1, 6, 7, rows, 1)
    &&& tp[14] is U16 && ff::date_col_at(tp, 1, 14, 15, rows, 4)
    &&& tp[21] is U8 && ff::int_col_at(tp, 1, 21, 22, rows, 6)
    &&& tp[23] is U32 && tp[24] is U64
    &&& tp[25] is U64 && ff::u64s(tp[25]).len() == 1
    &&& fi::common::keyidx::keyidx_ok(ff::u32s(tp[4]), ff::i64s(tp[5]), ff::u32s(tp[23]), ff::u64s(tp[24]),
            ff::u64s(tp[0])[1] as int, ff::u64s(tp[25])[0], rows.len() as int)
}

proof fn lemma_or_cols(tp: Seq<PartView>, rel: Seq<Row>)
    requires fi::orders_ok(tp, rel),
    ensures
        or_cols(tp, fi::orders_rows(tp, rel)),
        fi::table_layout_ok(tp, rel.len() as int),
        ff::perm_col_at(tp, 1, 2, 3, rel.len() as int),
{
}

pub open spec fn or_fields(m: M, tp: Seq<PartView>) -> bool {
    &&& m.o_key_c == pv_u32(tp[4]) && m.o_key_b == pv_i64(tp[5])
    &&& m.o_cust_c == pv_u32(tp[6]) && m.o_cust_b == pv_i64(tp[7])
    &&& m.o_date_c == pv_u16(tp[14]) && m.o_date_b == pv_i64(tp[15])
    &&& m.o_sp_c == pv_u8(tp[21]) && m.o_sp_b == pv_i64(tp[22])
    &&& m.o_ic == pv_u32(tp[23]) && m.o_ib == pv_u64(tp[24])
}

proof fn lemma_or_row(tp: Seq<PartView>, rel: Seq<Row>, t: Seq<Row>, m: M, q: int)
    requires
        or_cols(tp, fi::orders_rows(tp, rel)),
        ff::groups_part_ok(tp[1], rel.len() as int, m.o_bs),
        m.o_n == rel.len(),
        m.o_map == fi::orders_map(tp, m.o_n),
        ff::is_perm(m.o_map, m.o_n),
        or_fields(m, tp),
        rel == proj_all(t, fd::stored_cols_t1()),
        rows_in_columns(rel, fd::stored_columns_t1()),
        0 <= q < m.o_n,
    ensures
        proj(t[m.o_map[q]], ocols()) == orow(m, q),
        fi::orders_rows(tp, rel)[q][0] == Val::Int(okey(m, q)),
        in_i64(okey(m, q)), in_i64(ocust(m, q)), in_i64(osp(m, q)),
        crate::spec::datetime::date_valid(odate(m, q)), in_i64(odate(m, q)),
{
    let n = m.o_n;
    let bs = m.o_bs;
    let rows = fi::orders_rows(tp, rel);
    let i = m.o_map[q];
    assert(0 <= i < n);
    lemma_proj_all_index(t, fd::stored_cols_t1());
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[5], tp[4], q);
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[7], tp[6], q);
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[15], tp[14], q);
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[22], tp[21], q);
    assert(rows[q] == rel[i]);
    assert(rows[q][0] == Val::Int(okey(m, q)));
    assert(rows[q][1] == Val::Int(ocust(m, q)));
    assert(rows[q][4] == Val::Date(odate(m, q)));
    assert(rows[q][6] == Val::Int(osp(m, q)));
    assert(rel[i] == proj(t[i], fd::stored_cols_t1()));
    assert(t[i][0] == rel[i][0]);
    assert(t[i][1] == rel[i][1]);
    assert(t[i][4] == rel[i][4]);
    assert(t[i][7] == rel[i][6]);
    assert(proj(t[i], ocols()) =~= orow(m, q));
    assert(value_in_column(rel[i][0], fd::stored_columns_t1()[0]));
    assert(value_in_column(rel[i][1], fd::stored_columns_t1()[1]));
    assert(value_in_column(rel[i][4], fd::stored_columns_t1()[4]));
    assert(value_in_column(rel[i][6], fd::stored_columns_t1()[6]));
}

pub open spec fn or_ok(m: M, db: Database) -> bool {
    &&& 1 <= m.o_bs && 0 <= m.o_n && m.o_n + m.o_bs <= u64::MAX
    &&& m.o_nb * m.o_bs >= m.o_n && (m.o_nb > 0 ==> (m.o_nb - 1) * m.o_bs < m.o_n) && m.o_nb >= 0
    &&& m.o_key_c.len() == m.o_n && m.o_key_b.len() == m.o_nb
    &&& m.o_cust_c.len() == m.o_n && m.o_cust_b.len() == m.o_nb
    &&& m.o_date_c.len() == m.o_n && m.o_date_b.len() == m.o_nb
    &&& m.o_sp_c.len() == m.o_n && m.o_sp_b.len() == m.o_nb
    &&& m.o_n == db.tables[1].len()
    &&& ff::is_perm(m.o_map, m.o_n)
    &&& forall|q: int| 0 <= q < m.o_n ==> #[trigger] proj(db.tables[1][m.o_map[q]], ocols()) == orow(m, q)
    &&& forall|q: int| 0 <= q < m.o_n ==> {
        &&& in_i64(#[trigger] okey(m, q)) && in_i64(ocust(m, q)) && in_i64(osp(m, q))
        &&& crate::spec::datetime::date_valid(odate(m, q)) && in_i64(odate(m, q))
    }
    &&& fi::common::keyidx::keyidx_ok(m.o_key_c, m.o_key_b, m.o_ic, m.o_ib, m.o_bs, m.o_kind, m.o_n)
}

/// The orders stored rows and their key column (for the cluster flag).
pub open spec fn or_keys(sv: StoresView, db: Database) -> bool {
    let orows = fi::orders_rows(fparts(sv).subrange(48, 74), fd::stored_relations(db)[1]);
    &&& orows.len() == model_of(sv).o_n
    &&& forall|q: int| 0 <= q < model_of(sv).o_n ==> #[trigger] orows[q][0] == Val::Int(okey(model_of(sv), q))
}

proof fn lemma_orders(sv: StoresView, db: Database)
    requires
        fi::represents(fparts(sv), fd::stored_relations(db)),
        db.schema == schema_spec(),
        db_wf(db),
    ensures
        or_ok(model_of(sv), db),
        or_keys(sv, db),
        fparts(sv)[F_O_LAYOUT as int] is U64 && pv_u64(fparts(sv)[F_O_LAYOUT as int]).len() == 2,
        fparts(sv)[F_O_KEY_C as int] is U32 && fparts(sv)[F_O_KEY_B as int] is I64,
        fparts(sv)[F_O_CUST_C as int] is U32 && fparts(sv)[F_O_CUST_B as int] is I64,
        fparts(sv)[F_O_DATE_C as int] is U16 && fparts(sv)[F_O_DATE_B as int] is I64,
        fparts(sv)[F_O_SP_C as int] is U8 && fparts(sv)[F_O_SP_B as int] is I64,
        fparts(sv)[F_O_IDX_C as int] is U32 && fparts(sv)[F_O_IDX_B as int] is U64,
        fparts(sv)[F_O_IDX_KIND as int] is U64 && pv_u64(fparts(sv)[F_O_IDX_KIND as int]).len() == 1,
{
    let m = model_of(sv);
    let f = fparts(sv);
    let rels = fd::stored_relations(db);
    let tp = f.subrange(48, 74);
    let rel = rels[1];
    let t = db.tables[1];
    lemma_or_cols(tp, rel);
    fd::lemma_stored_relations(db);
    fd::lemma_declared_schema();
    let n = rel.len() as int;
    let bs = ff::u64s(tp[0])[1] as int;
    assert(tp[0] == f[48] && tp[1] == f[49]);
    assert(pv_u64(f[48]) == ff::u64s(tp[0]));
    assert(m.o_n == n && m.o_bs == bs);
    assert(tp[4] == f[52] && tp[5] == f[53] && tp[6] == f[54] && tp[7] == f[55] && tp[14] == f[62] && tp[15] == f[63]);
    assert(tp[21] == f[69] && tp[22] == f[70] && tp[23] == f[71] && tp[24] == f[72] && tp[25] == f[73]);
    assert(or_fields(m, tp));
    assert(m.o_kind == ff::u64s(tp[25])[0]);
    lemma_fgroups(tp[1], n, bs, m.o_nb);
    assert(rel == proj_all(t, fd::stored_cols_t1()));
    assert forall|q: int| 0 <= q < m.o_n implies #[trigger] proj(db.tables[1][m.o_map[q]], ocols()) == orow(m, q) by {
        lemma_or_row(tp, rel, t, m, q);
    }
    assert forall|q: int| 0 <= q < m.o_n implies {
        &&& in_i64(#[trigger] okey(m, q)) && in_i64(ocust(m, q)) && in_i64(osp(m, q))
        &&& crate::spec::datetime::date_valid(odate(m, q)) && in_i64(odate(m, q))
    } by {
        lemma_or_row(tp, rel, t, m, q);
    }
    let orows = fi::orders_rows(tp, rel);
    assert forall|q: int| 0 <= q < m.o_n implies #[trigger] orows[q][0] == Val::Int(okey(m, q)) by {
        lemma_or_row(tp, rel, t, m, q);
    }
}

// ------------------------------------------------------------------------------------------------ customer

pub open spec fn cu_cols(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp[2] is U32 && cf::int_col_at(tp, 1, 2, 3, rel, 0)
    &&& tp[14] is U8 && cf::dict_col_at(tp, 1, 14, 15, 16, 17, rel, 6)
    &&& tp[20] is U64 && cf::u64s(tp[20]).len() == 1
    &&& ci::common::keyidx::keyidx_ok(cf::u32s(tp[2]), cf::i64s(tp[3]), Seq::<u32>::empty(), Seq::<u64>::empty(),
            cf::u64s(tp[0])[1] as int, cf::u64s(tp[20])[0], rel.len() as int)
}

proof fn lemma_cu_cols(tp: Seq<PartView>, rel: Seq<Row>)
    requires ci::customer_ok(tp, rel),
    ensures cu_cols(tp, rel), ci::table_layout_ok(tp, rel.len() as int),
{
}

pub open spec fn cu_fields(m: M, tp: Seq<PartView>) -> bool {
    &&& m.c_key_c == pv_u32(tp[2]) && m.c_key_b == pv_i64(tp[3])
    &&& m.c_seg_c == pv_u8(tp[14]) && m.c_seg_b == pv_u64(tp[15])
    &&& m.d_off == pv_u64(tp[16]) && m.d_bytes == pv_u8(tp[17])
}

proof fn lemma_cu_row(tp: Seq<PartView>, rel: Seq<Row>, t: Seq<Row>, m: M, c: int)
    requires
        cu_cols(tp, rel),
        cf::groups_part_ok(tp[1], rel.len() as int, m.c_bs),
        m.c_n == rel.len(),
        cu_fields(m, tp),
        rel == proj_all(t, cd::stored_cols_t0()),
        rows_in_columns(rel, cd::stored_columns_t0()),
        0 <= c < m.c_n,
    ensures
        proj(t[c], ccols()) == crow(m, c),
        in_i64(ckey(m, c)),
        0 <= cseg(m, c) < dict_n(m),
{
    let n = m.c_n;
    let bs = m.c_bs;
    lemma_proj_all_index(t, cd::stored_cols_t0());
    ci::common::read::lemma_for_row(tp[1], n, bs, tp[3], tp[2], c);
    ci::common::read::lemma_for_row(tp[1], n, bs, tp[15], tp[14], c);
    assert(rel[c][0] == Val::Int(ckey(m, c)));
    assert(rel[c][6] == Val::Text(segtext(m, c)));
    assert(rel[c] == proj(t[c], cd::stored_cols_t0()));
    assert(t[c][0] == rel[c][0]);
    assert(t[c][6] == rel[c][6]);
    assert(proj(t[c], ccols()) =~= crow(m, c));
    assert(value_in_column(rel[c][0], cd::stored_columns_t0()[0]));
}

pub open spec fn cu_ok(m: M, db: Database) -> bool {
    &&& 1 <= m.c_bs && 0 <= m.c_n && m.c_n + m.c_bs <= u64::MAX
    &&& m.c_nb * m.c_bs >= m.c_n && (m.c_nb > 0 ==> (m.c_nb - 1) * m.c_bs < m.c_n) && m.c_nb >= 0
    &&& m.c_key_c.len() == m.c_n && m.c_key_b.len() == m.c_nb
    &&& m.c_seg_c.len() == m.c_n && m.c_seg_b.len() == m.c_nb
    &&& m.d_off.len() >= 1
    &&& m.c_n == db.tables[2].len()
    &&& forall|c: int| 0 <= c < m.c_n ==> #[trigger] proj(db.tables[2][c], ccols()) == crow(m, c)
    &&& forall|c: int| 0 <= c < m.c_n ==> in_i64(#[trigger] ckey(m, c)) && 0 <= cseg(m, c) < dict_n(m)
    &&& cf::text_parts_wf(m.d_off, m.d_bytes, dict_n(m))
    &&& cf::dict_sorted(m.d_off, m.d_bytes, dict_n(m))
    &&& ci::common::keyidx::keyidx_ok(m.c_key_c, m.c_key_b, Seq::<u32>::empty(), Seq::<u64>::empty(), m.c_bs, m.c_kind, m.c_n)
}

proof fn lemma_customer(sv: StoresView, db: Database)
    requires
        ci::represents(sv.custpart, cd::stored_relations(db)),
        db.schema == schema_spec(),
        db_wf(db),
    ensures
        cu_ok(model_of(sv), db),
        sv.custpart.len() > 20,
        sv.custpart[C_LAYOUT as int] is U64 && pv_u64(sv.custpart[C_LAYOUT as int]).len() == 2,
        sv.custpart[C_KEY_C as int] is U32 && sv.custpart[C_KEY_B as int] is I64,
        sv.custpart[C_SEG_C as int] is U8 && sv.custpart[C_SEG_B as int] is U64,
        sv.custpart[C_DICT_OFF as int] is U64 && sv.custpart[C_DICT_BYTES as int] is U8,
        sv.custpart[C_IDX_KIND as int] is U64 && pv_u64(sv.custpart[C_IDX_KIND as int]).len() == 1,
{
    let m = model_of(sv);
    let p = sv.custpart;
    let rels = cd::stored_relations(db);
    let tp = p.subrange(0, 21);
    let rel = rels[0];
    let t = db.tables[2];
    lemma_cu_cols(tp, rel);
    cd::lemma_stored_relations(db);
    cd::lemma_declared_schema();
    let n = rel.len() as int;
    let bs = cf::u64s(tp[0])[1] as int;
    assert(tp[0] == p[0] && tp[1] == p[1] && tp[2] == p[2] && tp[3] == p[3]);
    assert(tp[14] == p[14] && tp[15] == p[15] && tp[16] == p[16] && tp[17] == p[17] && tp[20] == p[20]);
    assert(pv_u64(p[0]) == cf::u64s(tp[0]));
    assert(m.c_n == n && m.c_bs == bs);
    assert(cu_fields(m, tp));
    assert(m.c_kind == cf::u64s(tp[20])[0]);
    lemma_cgroups(tp[1], n, bs, m.c_nb);
    assert(rel == proj_all(t, cd::stored_cols_t0()));
    assert(m.d_off == cf::u64s(tp[16]) && m.d_bytes == cf::u8s(tp[17]));
    assert forall|c: int| 0 <= c < m.c_n implies #[trigger] proj(db.tables[2][c], ccols()) == crow(m, c) by {
        lemma_cu_row(tp, rel, t, m, c);
    }
    assert forall|c: int| 0 <= c < m.c_n implies in_i64(#[trigger] ckey(m, c)) && 0 <= cseg(m, c) < dict_n(m) by {
        lemma_cu_row(tp, rel, t, m, c);
    }
}

// ------------------------------------------------------------------------------------------------ primary keys

/// The orders primary key at the part level: distinct stored positions hold distinct `o_orderkey`.
proof fn lemma_orders_pk(m: M, db: Database)
    requires
        or_ok(m, db),
        db.schema == schema_spec(),
        db_wf(db),
        constraints_hold(declared_db(db)),
    ensures
        forall|a: int, b: int| 0 <= a < m.o_n && 0 <= b < m.o_n && a != b ==> #[trigger] okey(m, a) != #[trigger] okey(m, b),
{
    let ddb = declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    fd::lemma_declared_schema();
    assert(declared_schema()[1].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert forall|a: int, b: int| 0 <= a < m.o_n && 0 <= b < m.o_n && a != b implies #[trigger] okey(m, a) != #[trigger] okey(m, b) by {
        if okey(m, a) == okey(m, b) {
            let (ia, ib) = (m.o_map[a], m.o_map[b]);
            assert(ff::is_perm(m.o_map, m.o_n));
            assert(ia != ib);
            let t = db.tables[1];
            assert(proj(t[ia], ocols()) == orow(m, a));
            assert(proj(t[ib], ocols()) == orow(m, b));
            assert(proj(t[ia], ocols())[0] == t[ia][0]);
            assert(proj(t[ib], ocols())[0] == t[ib][0]);
            assert(key_of(t[ia], seq![0nat]) =~= key_of(t[ib], seq![0nat]));
            lemma_row_not_distinct_refl(key_of(t[ia], seq![0nat]));
            assert(ddb.tables[1] == t);
            lemma_primary_key_identifies(ddb, 1, 0, seq![0nat], true, ia, ib);
        }
    }
}

/// The customer primary key at the part level.
proof fn lemma_customer_pk(m: M, db: Database)
    requires
        cu_ok(m, db),
        db.schema == schema_spec(),
        db_wf(db),
        constraints_hold(declared_db(db)),
    ensures
        forall|a: int, b: int| 0 <= a < m.c_n && 0 <= b < m.c_n && a != b ==> #[trigger] ckey(m, a) != #[trigger] ckey(m, b),
{
    let ddb = declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    fd::lemma_declared_schema();
    assert(declared_schema()[2].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert forall|a: int, b: int| 0 <= a < m.c_n && 0 <= b < m.c_n && a != b implies #[trigger] ckey(m, a) != #[trigger] ckey(m, b) by {
        if ckey(m, a) == ckey(m, b) {
            let t = db.tables[2];
            assert(proj(t[a], ccols()) == crow(m, a));
            assert(proj(t[b], ccols()) == crow(m, b));
            assert(proj(t[a], ccols())[0] == t[a][0]);
            assert(proj(t[b], ccols())[0] == t[b][0]);
            assert(key_of(t[a], seq![0nat]) =~= key_of(t[b], seq![0nat]));
            lemma_row_not_distinct_refl(key_of(t[a], seq![0nat]));
            assert(ddb.tables[2] == t);
            lemma_primary_key_identifies(ddb, 2, 0, seq![0nat], true, a, b);
        }
    }
}

// ------------------------------------------------------------------------------------------------ clustering

/// Under the orders primary key, `opos` is the unique position of a key (or `o_n`).
pub proof fn lemma_opos(m: M, k: int)
    requires
        forall|a: int, b: int| 0 <= a < m.o_n && 0 <= b < m.o_n && a != b ==> #[trigger] okey(m, a) != #[trigger] okey(m, b),
        m.o_n >= 0,
    ensures
        0 <= opos(m, k) <= m.o_n,
        opos(m, k) < m.o_n ==> okey(m, opos(m, k)) == k,
        forall|q: int| 0 <= q < m.o_n && q != opos(m, k) ==> #[trigger] okey(m, q) != k,
{
    if exists|q: int| 0 <= q < m.o_n && #[trigger] okey(m, q) == k {
        let p = choose|q: int| 0 <= q < m.o_n && #[trigger] okey(m, q) == k;
        assert(opos(m, k) == p);
        assert forall|q: int| 0 <= q < m.o_n && q != p implies #[trigger] okey(m, q) != k by {
            assert(okey(m, q) != okey(m, p));
        }
    }
}

/// The cluster flag gives a nondecreasing order position along the stored lineitem rows.
proof fn lemma_cluster(sv: StoresView, db: Database)
    requires
        fi::represents(fparts(sv), fd::stored_relations(db)),
        li_keys(sv, db),
        or_keys(sv, db),
        model_of(sv).o_n >= 0,
        forall|a: int, b: int| 0 <= a < model_of(sv).o_n && 0 <= b < model_of(sv).o_n && a != b
            ==> #[trigger] okey(model_of(sv), a) != #[trigger] okey(model_of(sv), b),
    ensures cluster_ok(model_of(sv)),
{
    let m = model_of(sv);
    let f = fparts(sv);
    let rels = fd::stored_relations(db);
    if m.cluster == 1 {
        assert(ff::u64s(f[74]) == pv_u64(f[74]));
        let lrows = fi::lineitem_rows(f.subrange(0, 48), rels[0]);
        let orows = fi::orders_rows(f.subrange(48, 74), rels[1]);
        assert(fi::cluster::clustered(lrows, orows));
        assert forall|j: int| 0 <= j < m.l_n - 1 implies #[trigger] lpos(m, j) <= lpos(m, j + 1) by {
            assert(fi::cluster::cluster_step(lrows, orows, j));
            let (k1, k2) = (lkey(m, j), lkey(m, j + 1));
            assert(lrows[j][0] == Val::Int(k1));
            assert(lrows[j + 1][0] == Val::Int(k2));
            lemma_opos(m, k1);
            lemma_opos(m, k2);
            fi::cluster::lemma_order_pos_at(orows, Val::Int(k1), opos(m, k1));
            fi::cluster::lemma_order_pos_at(orows, Val::Int(k2), opos(m, k2));
        }
    }
}

// ------------------------------------------------------------------------------------------------ the model

/// li_okruns' stored relations are facts' (the same declaration).
proof fn lemma_same_relations(db: Database)
    ensures lrd::stored_relations(db) == fd::stored_relations(db),
{
    assert(lrd::stored_cols_t0() =~= fd::stored_cols_t0());
    assert(lrd::stored_cols_t1() =~= fd::stored_cols_t1());
    assert(lrd::stored_relations(db) =~= fd::stored_relations(db));
}

/// Storage `li_okruns` gives facts' `represents` over its first 75 parts and the run starts over the model.
proof fn lemma_okruns(sv: StoresView, db: Database)
    requires lr::represents(sv.li_okruns, lrd::stored_relations(db)),
    ensures
        fi::represents(fparts(sv), fd::stored_relations(db)),
        sv.li_okruns.len() == 76 && sv.li_okruns[R_STARTS as int] is U32,
        runs_ok(model_of(sv)),
{
    lemma_same_relations(db);
    let all = sv.li_okruns;
    let f = fparts(sv);
    let m = model_of(sv);
    assert(lr::runs_ok(all));
    assert(f[F_L_LAYOUT as int] == all[F_L_LAYOUT as int]);
    assert(f[F_L_KEY_C as int] == all[F_L_KEY_C as int]);
    assert(f[F_L_KEY_B as int] == all[F_L_KEY_B as int]);
    assert(lr::starts(all) == m.l_st);
    assert(m.l_n == lr::li_rows(all));
    assert forall|s: int| #[trigger] lkey(m, s) == lr::okey_at(all, s) by {}
    assert forall|k: int| 0 <= k < m.l_st.len() - 1 implies #[trigger] run_ok(m, k) by {
        assert(lr::run_ok(all, k));
    }
}

/// Every database bound to the parts gives the model facts and reads its tables through the model.
pub proof fn lemma_model(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        model_ok(model_of(sv)),
        rel_ok(model_of(sv), db),
        kinds_ok(sv),
{
    let m = model_of(sv);
    assert(crate::gendb_entry::stores::stored_ok(sv, db));
    lemma_okruns(sv, db);
    lemma_lineitem(sv, db);
    lemma_orders(sv, db);
    lemma_customer(sv, db);
    lemma_orders_pk(m, db);
    lemma_customer_pk(m, db);
    lemma_cluster(sv, db);
}

} // verus!
