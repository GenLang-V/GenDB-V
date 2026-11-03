//! What every database bound to the parts gives about the model (`model`): the part kinds the extent reads need,
//! the layout and decoded values (`facts` represents lineitem and orders through row maps; `custpart` represents
//! part, `suppliers` partsupp, supplier and nation in canonical order), the declared primary keys at the part level,
//! and the key indexes. Per table: one predicate unpacks only the columns read (`*_cols`), one lemma states a row,
//! one collects the table's facts; `lemma_model` combines them.
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
use crate::stores::suppliers::interface as si;
use crate::stores::facts::declaration as fd;
use crate::stores::factspk::interface as ki;
use crate::stores::factspk::declaration as kd;
use crate::stores::custpart::declaration as cd;
use crate::stores::suppliers::declaration as sd;
use crate::stores::partsig::interface as gi;
use crate::stores::partsig::declaration as gd;
use fi::common::colfmt as ff;
use ci::common::colfmt as cf;
use si::common::colfmt as sf;
use super::model::*;
use super::cols::kinds_ok;

verus! {

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

proof fn lemma_sgroups(p: PartView, n: int, bs: int, nb: int)
    requires sf::groups_part_ok(p, n, bs), nb == sf::u64s(p).len() - 1,
    ensures nb >= 0, nb * bs >= n, nb > 0 ==> (nb - 1) * bs < n,
{
    sf::lemma_uniform_groups(p, n, bs);
    sf::lemma_nblocks(n, bs);
}

/// The groups part has one more entry than the base part of a column over it.
proof fn lemma_fbases(p: PartView, base: PartView, codes: PartView, n: int)
    requires ff::for_shape(ff::u64s(p), base, codes, n),
    ensures ff::u64s(p).len() - 1 == match base { PartView::I64(s) => s.len() as int, PartView::U64(s) => s.len() as int, _ => -1 },
{
}

// ------------------------------------------------------------------------------------------------ lineitem

/// The lineitem columns this query reads, over the stored rows.
pub open spec fn li_cols(tp: Seq<PartView>, rows: Seq<Row>) -> bool {
    &&& tp[4] is U32 && ff::int_col_at(tp, 1, 4, 5, rows, 0)
    &&& tp[6] is U32 && ff::int_col_at(tp, 1, 6, 7, rows, 1)
    &&& tp[8] is U32 && ff::int_col_at(tp, 1, 8, 9, rows, 2)
    &&& tp[12] is U16 && ff::num_col_at(tp, 1, 12, 13, rows, 4, 2)
    &&& tp[14] is U32 && ff::num_col_at(tp, 1, 14, 15, rows, 5, 2)
    &&& tp[16] is U8 && ff::num_col_at(tp, 1, 16, 17, rows, 6, 2)
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
    &&& m.l_ok_c == pv_u32(tp[4]) && m.l_ok_b == pv_i64(tp[5])
    &&& m.l_pk_c == pv_u32(tp[6]) && m.l_pk_b == pv_i64(tp[7])
    &&& m.l_sk_c == pv_u32(tp[8]) && m.l_sk_b == pv_i64(tp[9])
    &&& m.l_qty_c == pv_u16(tp[12]) && m.l_qty_b == pv_i64(tp[13])
    &&& m.l_price_c == pv_u32(tp[14]) && m.l_price_b == pv_i64(tp[15])
    &&& m.l_disc_c == pv_u8(tp[16]) && m.l_disc_b == pv_i64(tp[17])
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
        fi::lineitem_rows(tp, rel)[j][0] == Val::Int(lok(m, j)),
        in_i64(lok(m, j)) && in_i64(lpk(m, j)) && in_i64(lsk(m, j)),
        num15(lqty(m, j)) && num15(lprice(m, j)) && num15(ldisc(m, j)),
{
    let n = m.l_n;
    let bs = m.l_bs;
    let rows = fi::lineitem_rows(tp, rel);
    let i = m.l_map[j];
    assert(0 <= i < n);
    lemma_proj_all_index(t, fd::stored_cols_t0());
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[5], tp[4], j);
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[7], tp[6], j);
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[9], tp[8], j);
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[13], tp[12], j);
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[15], tp[14], j);
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[17], tp[16], j);
    assert(rows[j] == rel[i]);
    assert(rows[j][0] == Val::Int(lok(m, j)));
    assert(rows[j][1] == Val::Int(lpk(m, j)));
    assert(rows[j][2] == Val::Int(lsk(m, j)));
    assert(rows[j][4] == Val::Num { coeff: lqty(m, j), scale: 2 });
    assert(rows[j][5] == Val::Num { coeff: lprice(m, j), scale: 2 });
    assert(rows[j][6] == Val::Num { coeff: ldisc(m, j), scale: 2 });
    assert(rel[i] == proj(t[i], fd::stored_cols_t0()));
    assert(t[i][0] == rel[i][0]);
    assert(t[i][1] == rel[i][1]);
    assert(t[i][2] == rel[i][2]);
    assert(t[i][4] == rel[i][4]);
    assert(t[i][5] == rel[i][5]);
    assert(t[i][6] == rel[i][6]);
    assert(proj(t[i], lcols()) =~= lrow(m, j));
    assert(value_in_column(rel[i][0], fd::stored_columns_t0()[0]));
    assert(value_in_column(rel[i][1], fd::stored_columns_t0()[1]));
    assert(value_in_column(rel[i][2], fd::stored_columns_t0()[2]));
    assert(value_in_column(rel[i][4], fd::stored_columns_t0()[4]));
    assert(value_in_column(rel[i][5], fd::stored_columns_t0()[5]));
    assert(value_in_column(rel[i][6], fd::stored_columns_t0()[6]));
}

/// Lineitem facts of the model.
pub open spec fn li_ok(m: M, db: Database) -> bool {
    &&& frame_ok(m.l_n, m.l_bs, m.l_nb)
    &&& m.l_ok_c.len() == m.l_n && m.l_ok_b.len() == m.l_nb
    &&& m.l_pk_c.len() == m.l_n && m.l_pk_b.len() == m.l_nb
    &&& m.l_sk_c.len() == m.l_n && m.l_sk_b.len() == m.l_nb
    &&& m.l_qty_c.len() == m.l_n && m.l_qty_b.len() == m.l_nb
    &&& m.l_price_c.len() == m.l_n && m.l_price_b.len() == m.l_nb
    &&& m.l_disc_c.len() == m.l_n && m.l_disc_b.len() == m.l_nb
    &&& m.l_n == db.tables[0].len()
    &&& ff::is_perm(m.l_map, m.l_n)
    &&& forall|j: int| 0 <= j < m.l_n ==> #[trigger] proj(db.tables[0][m.l_map[j]], lcols()) == lrow(m, j)
    &&& forall|j: int| 0 <= j < m.l_n ==> {
        &&& in_i64(#[trigger] lok(m, j)) && in_i64(lpk(m, j)) && in_i64(lsk(m, j))
        &&& num15(lqty(m, j)) && num15(lprice(m, j)) && num15(ldisc(m, j))
    }
}

proof fn lemma_lineitem(sv: StoresView, db: Database)
    requires
        fi::represents(fx(sv), fd::stored_relations(db)),
        db.schema == schema_spec(),
        db_wf(db),
    ensures
        li_ok(model_of(sv), db),
        fx(sv)[F_L_LAYOUT as int] is U64 && pv_u64(fx(sv)[F_L_LAYOUT as int]).len() == 2,
        fx(sv)[F_L_OK_C as int] is U32 && fx(sv)[F_L_OK_B as int] is I64,
        fx(sv)[F_L_PK_C as int] is U32 && fx(sv)[F_L_PK_B as int] is I64,
        fx(sv)[F_L_SK_C as int] is U32 && fx(sv)[F_L_SK_B as int] is I64,
        fx(sv)[F_L_QTY_C as int] is U16 && fx(sv)[F_L_QTY_B as int] is I64,
        fx(sv)[F_L_PRICE_C as int] is U32 && fx(sv)[F_L_PRICE_B as int] is I64,
        fx(sv)[F_L_DISC_C as int] is U8 && fx(sv)[F_L_DISC_B as int] is I64,
        fi::lineitem_rows(fx(sv).subrange(0, 48), fd::stored_relations(db)[0]).len() == model_of(sv).l_n,
        forall|j: int| 0 <= j < model_of(sv).l_n ==>
            #[trigger] fi::lineitem_rows(fx(sv).subrange(0, 48), fd::stored_relations(db)[0])[j][0] == Val::Int(lok(model_of(sv), j)),
{
    let m = model_of(sv);
    let f = fx(sv);
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
    assert(tp[4] == f[4] && tp[5] == f[5] && tp[6] == f[6] && tp[7] == f[7] && tp[8] == f[8] && tp[9] == f[9]);
    assert(tp[12] == f[12] && tp[13] == f[13] && tp[14] == f[14] && tp[15] == f[15] && tp[16] == f[16] && tp[17] == f[17]);
    assert(li_fields(m, tp));
    lemma_fgroups(tp[1], n, bs, m.l_nb);
    assert(rel == proj_all(t, fd::stored_cols_t0()));
    assert(db.tables.len() == 8);
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] proj(db.tables[0][m.l_map[j]], lcols()) == lrow(m, j) by {
        lemma_li_row(tp, rel, t, m, j);
    }
    assert forall|j: int| 0 <= j < m.l_n implies {
        &&& in_i64(#[trigger] lok(m, j)) && in_i64(lpk(m, j)) && in_i64(lsk(m, j))
        &&& num15(lqty(m, j)) && num15(lprice(m, j)) && num15(ldisc(m, j))
    } by {
        lemma_li_row(tp, rel, t, m, j);
    }
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] fi::lineitem_rows(tp, rel)[j][0] == Val::Int(lok(m, j)) by {
        lemma_li_row(tp, rel, t, m, j);
    }
}

// ------------------------------------------------------------------------------------------------ orders

pub open spec fn or_cols(tp: Seq<PartView>, rows: Seq<Row>) -> bool {
    &&& tp[4] is U32 && ff::int_col_at(tp, 1, 4, 5, rows, 0)
    &&& tp[14] is U16 && ff::date_col_at(tp, 1, 14, 15, rows, 4)
    &&& tp[16] is I64 && ff::zone_at(tp, 1, 14, 15, 16)
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
    &&& m.o_date_c == pv_u16(tp[14]) && m.o_date_b == pv_i64(tp[15]) && m.o_date_z == pv_i64(tp[16])
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
        odate(m, q) <= m.o_date_z[q / m.o_bs],
        in_i64(okey(m, q)),
        crate::spec::datetime::date_valid(odate(m, q)), in_i64(odate(m, q)),
{
    let n = m.o_n;
    let bs = m.o_bs;
    let rows = fi::orders_rows(tp, rel);
    let i = m.o_map[q];
    assert(0 <= i < n);
    lemma_proj_all_index(t, fd::stored_cols_t1());
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[5], tp[4], q);
    fi::common::read::lemma_for_row(tp[1], n, bs, tp[15], tp[14], q);
    assert(rows[q] == rel[i]);
    assert(rows[q][0] == Val::Int(okey(m, q)));
    assert(rows[q][4] == Val::Date(odate(m, q)));
    assert(ff::in_group(ff::u64s(tp[1]), q / bs, q));
    assert(ff::base_at(tp[15], q / bs) + ff::code_at(tp[14], q) <= ff::i64s(tp[16])[q / bs]);
    assert(rel[i] == proj(t[i], fd::stored_cols_t1()));
    assert(t[i][0] == rel[i][0]);
    assert(t[i][4] == rel[i][4]);
    assert(proj(t[i], ocols()) =~= orow(m, q));
    assert(value_in_column(rel[i][0], fd::stored_columns_t1()[0]));
    assert(value_in_column(rel[i][4], fd::stored_columns_t1()[4]));
}

pub open spec fn or_ok(m: M, db: Database) -> bool {
    &&& frame_ok(m.o_n, m.o_bs, m.o_nb)
    &&& m.o_key_c.len() == m.o_n && m.o_key_b.len() == m.o_nb
    &&& m.o_date_c.len() == m.o_n && m.o_date_b.len() == m.o_nb
    &&& m.o_n == db.tables[1].len()
    &&& ff::is_perm(m.o_map, m.o_n)
    &&& forall|q: int| 0 <= q < m.o_n ==> #[trigger] proj(db.tables[1][m.o_map[q]], ocols()) == orow(m, q)
    &&& forall|q: int| 0 <= q < m.o_n ==> in_i64(#[trigger] okey(m, q)) && crate::spec::datetime::date_valid(odate(m, q)) && in_i64(odate(m, q))
    &&& fi::common::keyidx::keyidx_ok(m.o_key_c, m.o_key_b, m.o_ic, m.o_ib, m.o_bs, m.o_kind, m.o_n)
    &&& m.o_date_z.len() == m.o_nb
    &&& forall|q: int| 0 <= q < m.o_n ==> #[trigger] odate(m, q) <= m.o_date_z[q / m.o_bs]
}

proof fn lemma_orders(sv: StoresView, db: Database)
    requires
        fi::represents(fx(sv), fd::stored_relations(db)),
        db.schema == schema_spec(),
        db_wf(db),
    ensures
        or_ok(model_of(sv), db),
        fx(sv)[F_O_LAYOUT as int] is U64 && pv_u64(fx(sv)[F_O_LAYOUT as int]).len() == 2,
        fx(sv)[F_O_KEY_C as int] is U32 && fx(sv)[F_O_KEY_B as int] is I64,
        fx(sv)[F_O_DATE_C as int] is U16 && fx(sv)[F_O_DATE_B as int] is I64 && fx(sv)[F_O_DATE_Z as int] is I64,
        fx(sv)[F_O_IDX_C as int] is U32 && fx(sv)[F_O_IDX_B as int] is U64,
        fi::orders_rows(fx(sv).subrange(48, 74), fd::stored_relations(db)[1]).len() == model_of(sv).o_n,
        forall|q: int| 0 <= q < model_of(sv).o_n ==>
            #[trigger] fi::orders_rows(fx(sv).subrange(48, 74), fd::stored_relations(db)[1])[q][0] == Val::Int(okey(model_of(sv), q)),
        fx(sv)[F_O_IDX_KIND as int] is U64 && pv_u64(fx(sv)[F_O_IDX_KIND as int]).len() == 1,
{
    let m = model_of(sv);
    let f = fx(sv);
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
    assert(tp[4] == f[52] && tp[5] == f[53] && tp[14] == f[62] && tp[15] == f[63] && tp[16] == f[64]);
    assert(tp[23] == f[71] && tp[24] == f[72] && tp[25] == f[73]);
    assert(or_fields(m, tp));
    assert(m.o_kind == ff::u64s(tp[25])[0]);
    lemma_fgroups(tp[1], n, bs, m.o_nb);
    assert(rel == proj_all(t, fd::stored_cols_t1()));
    assert forall|q: int| 0 <= q < m.o_n implies #[trigger] proj(db.tables[1][m.o_map[q]], ocols()) == orow(m, q) by {
        lemma_or_row(tp, rel, t, m, q);
    }
    assert forall|q: int| 0 <= q < m.o_n implies in_i64(#[trigger] okey(m, q)) && crate::spec::datetime::date_valid(odate(m, q)) && in_i64(odate(m, q)) by {
        lemma_or_row(tp, rel, t, m, q);
    }
    assert forall|q: int| 0 <= q < m.o_n implies #[trigger] odate(m, q) <= m.o_date_z[q / m.o_bs] by {
        lemma_or_row(tp, rel, t, m, q);
    }
    assert forall|q: int| 0 <= q < m.o_n implies #[trigger] fi::orders_rows(tp, rel)[q][0] == Val::Int(okey(m, q)) by {
        lemma_or_row(tp, rel, t, m, q);
    }
    assert(m.o_date_z.len() == m.o_nb) by {
        assert(ff::zone_max_ok(ff::u64s(tp[1]), tp[15], tp[14], ff::i64s(tp[16])));
    }
}

// ------------------------------------------------------------------------------------------------ part

pub open spec fn pa_cols(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp[2] is U32 && cf::int_col_at(tp, 1, 2, 3, rel, 0)
    &&& cf::text_col_at(tp, 4, 5, rel, 1)
    &&& tp[28] is U64 && cf::u64s(tp[28]).len() == 1
    &&& ci::common::keyidx::keyidx_ok(cf::u32s(tp[2]), cf::i64s(tp[3]), Seq::<u32>::empty(), Seq::<u64>::empty(),
            cf::u64s(tp[0])[1] as int, cf::u64s(tp[28])[0], rel.len() as int)
}

proof fn lemma_pa_cols(tp: Seq<PartView>, rel: Seq<Row>)
    requires ci::part_ok(tp, rel),
    ensures pa_cols(tp, rel), ci::table_layout_ok(tp, rel.len() as int),
{
}

pub open spec fn pa_fields(m: M, tp: Seq<PartView>) -> bool {
    &&& m.p_key_c == pv_u32(tp[2]) && m.p_key_b == pv_i64(tp[3])
    &&& m.p_name_o == pv_u64(tp[4]) && m.p_name_y == pv_u8(tp[5])
}

proof fn lemma_pa_row(tp: Seq<PartView>, rel: Seq<Row>, t: Seq<Row>, m: M, c: int)
    requires
        pa_cols(tp, rel),
        cf::groups_part_ok(tp[1], rel.len() as int, m.p_bs),
        m.p_n == rel.len(),
        pa_fields(m, tp),
        rel == proj_all(t, cd::stored_cols_t1()),
        rows_in_columns(rel, cd::stored_columns_t1()),
        0 <= c < m.p_n,
    ensures
        proj(t[c], pcols()) == prow(m, c),
        in_i64(pkey(m, c)),
{
    let n = m.p_n;
    let bs = m.p_bs;
    lemma_proj_all_index(t, cd::stored_cols_t1());
    ci::common::read::lemma_for_row(tp[1], n, bs, tp[3], tp[2], c);
    assert(rel[c][0] == Val::Int(pkey(m, c)));
    assert(rel[c][1] == Val::Text(pname(m, c)));
    assert(rel[c] == proj(t[c], cd::stored_cols_t1()));
    assert(t[c][0] == rel[c][0]);
    assert(t[c][1] == rel[c][1]);
    assert(proj(t[c], pcols()) =~= prow(m, c));
    assert(value_in_column(rel[c][0], cd::stored_columns_t1()[0]));
}

pub open spec fn pa_ok(m: M, db: Database) -> bool {
    &&& frame_ok(m.p_n, m.p_bs, m.p_nb)
    &&& m.p_key_c.len() == m.p_n && m.p_key_b.len() == m.p_nb
    &&& cf::text_parts_wf(m.p_name_o, m.p_name_y, m.p_n)
    &&& m.p_n == db.tables[3].len()
    &&& forall|c: int| 0 <= c < m.p_n ==> #[trigger] proj(db.tables[3][c], pcols()) == prow(m, c)
    &&& forall|c: int| 0 <= c < m.p_n ==> in_i64(#[trigger] pkey(m, c))
    &&& ci::common::keyidx::keyidx_ok(m.p_key_c, m.p_key_b, Seq::<u32>::empty(), Seq::<u64>::empty(), m.p_bs, m.p_kind, m.p_n)
}

proof fn lemma_part(sv: StoresView, db: Database)
    requires
        ci::represents(sv.custpart, cd::stored_relations(db)),
        db.schema == schema_spec(),
        db_wf(db),
    ensures
        pa_ok(model_of(sv), db),
        sv.custpart.len() == 50,
        sv.custpart[C_P_LAYOUT as int] is U64 && pv_u64(sv.custpart[C_P_LAYOUT as int]).len() == 2,
        sv.custpart[C_P_KEY_C as int] is U32 && sv.custpart[C_P_KEY_B as int] is I64,
        sv.custpart[C_P_NAME_O as int] is U64 && sv.custpart[C_P_NAME_Y as int] is U8,
        sv.custpart[C_P_KIND as int] is U64 && pv_u64(sv.custpart[C_P_KIND as int]).len() == 1,
{
    let m = model_of(sv);
    let pp = sv.custpart;
    let rels = cd::stored_relations(db);
    let tp = pp.subrange(21, 50);
    let rel = rels[1];
    let t = db.tables[3];
    lemma_pa_cols(tp, rel);
    cd::lemma_stored_relations(db);
    cd::lemma_declared_schema();
    let n = rel.len() as int;
    let bs = cf::u64s(tp[0])[1] as int;
    assert(tp[0] == pp[21] && tp[1] == pp[22] && tp[2] == pp[23] && tp[3] == pp[24] && tp[4] == pp[25] && tp[5] == pp[26]);
    assert(tp[28] == pp[49]);
    assert(pv_u64(pp[21]) == cf::u64s(tp[0]));
    assert(m.p_n == n && m.p_bs == bs);
    assert(pa_fields(m, tp));
    assert(m.p_kind == cf::u64s(tp[28])[0]);
    lemma_cgroups(tp[1], n, bs, m.p_nb);
    assert(rel == proj_all(t, cd::stored_cols_t1()));
    assert(m.p_name_o == cf::u64s(tp[4]) && m.p_name_y == cf::u8s(tp[5]));
    assert forall|c: int| 0 <= c < m.p_n implies #[trigger] proj(db.tables[3][c], pcols()) == prow(m, c) by {
        lemma_pa_row(tp, rel, t, m, c);
    }
    assert forall|c: int| 0 <= c < m.p_n implies in_i64(#[trigger] pkey(m, c)) by {
        lemma_pa_row(tp, rel, t, m, c);
    }
}

// ------------------------------------------------------------------------------------------------ partsupp

pub open spec fn ps_cols(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp[2] is U32 && sf::int_col_at(tp, 1, 2, 3, rel, 0)
    &&& tp[4] is U32 && sf::int_col_at(tp, 1, 4, 5, rel, 1)
    &&& tp[8] is U32 && sf::num_col_at(tp, 1, 8, 9, rel, 3, 2)
    &&& tp[12] is U64 && sf::u64s(tp[12]).len() == 1
    &&& si::common::keyidx::keyidx_ok(sf::u32s(tp[2]), sf::i64s(tp[3]), Seq::<u32>::empty(), Seq::<u64>::empty(),
            sf::u64s(tp[0])[1] as int, sf::u64s(tp[12])[0], rel.len() as int)
}

proof fn lemma_ps_cols(tp: Seq<PartView>, rel: Seq<Row>)
    requires si::partsupp_ok(tp, rel),
    ensures ps_cols(tp, rel), si::table_layout_ok(tp, rel.len() as int),
{
}

pub open spec fn ps_fields(m: M, tp: Seq<PartView>) -> bool {
    &&& m.t_pk_c == pv_u32(tp[2]) && m.t_pk_b == pv_i64(tp[3])
    &&& m.t_sk_c == pv_u32(tp[4]) && m.t_sk_b == pv_i64(tp[5])
    &&& m.t_cost_c == pv_u32(tp[8]) && m.t_cost_b == pv_i64(tp[9])
}

proof fn lemma_ps_row(tp: Seq<PartView>, rel: Seq<Row>, t: Seq<Row>, m: M, x: int)
    requires
        ps_cols(tp, rel),
        sf::groups_part_ok(tp[1], rel.len() as int, m.t_bs),
        m.t_n == rel.len(),
        ps_fields(m, tp),
        rel == proj_all(t, sd::stored_cols_t0()),
        rows_in_columns(rel, sd::stored_columns_t0()),
        0 <= x < m.t_n,
    ensures
        proj(t[x], tcols()) == trow(m, x),
        in_i64(tpk(m, x)) && in_i64(tsk(m, x)) && num15(tcost(m, x)),
{
    let n = m.t_n;
    let bs = m.t_bs;
    lemma_proj_all_index(t, sd::stored_cols_t0());
    si::common::read::lemma_for_row(tp[1], n, bs, tp[3], tp[2], x);
    si::common::read::lemma_for_row(tp[1], n, bs, tp[5], tp[4], x);
    si::common::read::lemma_for_row(tp[1], n, bs, tp[9], tp[8], x);
    assert(rel[x][0] == Val::Int(tpk(m, x)));
    assert(rel[x][1] == Val::Int(tsk(m, x)));
    assert(rel[x][3] == Val::Num { coeff: tcost(m, x), scale: 2 });
    assert(rel[x] == proj(t[x], sd::stored_cols_t0()));
    assert(t[x][0] == rel[x][0]);
    assert(t[x][1] == rel[x][1]);
    assert(t[x][3] == rel[x][3]);
    assert(proj(t[x], tcols()) =~= trow(m, x));
    assert(value_in_column(rel[x][0], sd::stored_columns_t0()[0]));
    assert(value_in_column(rel[x][1], sd::stored_columns_t0()[1]));
    assert(value_in_column(rel[x][3], sd::stored_columns_t0()[3]));
}

pub open spec fn ps_ok(m: M, db: Database) -> bool {
    &&& frame_ok(m.t_n, m.t_bs, m.t_nb)
    &&& m.t_pk_c.len() == m.t_n && m.t_pk_b.len() == m.t_nb
    &&& m.t_sk_c.len() == m.t_n && m.t_sk_b.len() == m.t_nb
    &&& m.t_cost_c.len() == m.t_n && m.t_cost_b.len() == m.t_nb
    &&& m.t_n == db.tables[4].len()
    &&& forall|x: int| 0 <= x < m.t_n ==> #[trigger] proj(db.tables[4][x], tcols()) == trow(m, x)
    &&& forall|x: int| 0 <= x < m.t_n ==> in_i64(#[trigger] tpk(m, x)) && in_i64(tsk(m, x)) && num15(tcost(m, x))
    &&& si::common::keyidx::keyidx_ok(m.t_pk_c, m.t_pk_b, Seq::<u32>::empty(), Seq::<u64>::empty(), m.t_bs, m.t_kind, m.t_n)
}

/// The suppliers storage's tables and the parts the query reads.
proof fn lemma_partsupp(sv: StoresView, db: Database)
    requires
        si::represents(sv.suppliers, sd::stored_relations(db)),
        db.schema == schema_spec(),
        db_wf(db),
    ensures
        ps_ok(model_of(sv), db),
        sv.suppliers.len() == 48,
        sv.suppliers[S_PS_LAYOUT as int] is U64 && pv_u64(sv.suppliers[S_PS_LAYOUT as int]).len() == 2,
        sv.suppliers[S_PS_PK_C as int] is U32 && sv.suppliers[S_PS_PK_B as int] is I64,
        sv.suppliers[S_PS_SK_C as int] is U32 && sv.suppliers[S_PS_SK_B as int] is I64,
        sv.suppliers[S_PS_COST_C as int] is U32 && sv.suppliers[S_PS_COST_B as int] is I64,
        sv.suppliers[S_PS_KIND as int] is U64 && pv_u64(sv.suppliers[S_PS_KIND as int]).len() == 1,
{
    let m = model_of(sv);
    let pp = sv.suppliers;
    let rels = sd::stored_relations(db);
    let tp = pp.subrange(0, 13);
    let rel = rels[0];
    let t = db.tables[4];
    lemma_ps_cols(tp, rel);
    sd::lemma_stored_relations(db);
    sd::lemma_declared_schema();
    let n = rel.len() as int;
    let bs = sf::u64s(tp[0])[1] as int;
    assert(tp[0] == pp[0] && tp[1] == pp[1] && tp[2] == pp[2] && tp[3] == pp[3] && tp[4] == pp[4] && tp[5] == pp[5]);
    assert(tp[8] == pp[8] && tp[9] == pp[9] && tp[12] == pp[12]);
    assert(pv_u64(pp[0]) == sf::u64s(tp[0]));
    assert(m.t_n == n && m.t_bs == bs);
    assert(ps_fields(m, tp));
    assert(m.t_kind == sf::u64s(tp[12])[0]);
    lemma_sgroups(tp[1], n, bs, m.t_nb);
    assert(rel == proj_all(t, sd::stored_cols_t0()));
    assert forall|x: int| 0 <= x < m.t_n implies #[trigger] proj(db.tables[4][x], tcols()) == trow(m, x) by {
        lemma_ps_row(tp, rel, t, m, x);
    }
    assert forall|x: int| 0 <= x < m.t_n implies in_i64(#[trigger] tpk(m, x)) && in_i64(tsk(m, x)) && num15(tcost(m, x)) by {
        lemma_ps_row(tp, rel, t, m, x);
    }
}

// ------------------------------------------------------------------------------------------------ supplier

pub open spec fn su_cols(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp[2] is U32 && sf::int_col_at(tp, 1, 2, 3, rel, 0)
    &&& tp[8] is U8 && sf::int_col_at(tp, 1, 8, 9, rel, 3)
    &&& tp[16] is U64 && sf::u64s(tp[16]).len() == 1
    &&& si::common::keyidx::keyidx_ok(sf::u32s(tp[2]), sf::i64s(tp[3]), Seq::<u32>::empty(), Seq::<u64>::empty(),
            sf::u64s(tp[0])[1] as int, sf::u64s(tp[16])[0], rel.len() as int)
}

proof fn lemma_su_cols(tp: Seq<PartView>, rel: Seq<Row>)
    requires si::supplier_ok(tp, rel),
    ensures su_cols(tp, rel), si::table_layout_ok(tp, rel.len() as int),
{
}

pub open spec fn su_fields(m: M, tp: Seq<PartView>) -> bool {
    &&& m.s_key_c == pv_u32(tp[2]) && m.s_key_b == pv_i64(tp[3])
    &&& m.s_nk_c == pv_u8(tp[8]) && m.s_nk_b == pv_i64(tp[9])
}

proof fn lemma_su_row(tp: Seq<PartView>, rel: Seq<Row>, t: Seq<Row>, m: M, x: int)
    requires
        su_cols(tp, rel),
        sf::groups_part_ok(tp[1], rel.len() as int, m.s_bs),
        m.s_n == rel.len(),
        su_fields(m, tp),
        rel == proj_all(t, sd::stored_cols_t1()),
        rows_in_columns(rel, sd::stored_columns_t1()),
        0 <= x < m.s_n,
    ensures
        proj(t[x], scols()) == srow(m, x),
        in_i64(skey(m, x)) && in_i64(snk(m, x)),
{
    let n = m.s_n;
    let bs = m.s_bs;
    lemma_proj_all_index(t, sd::stored_cols_t1());
    si::common::read::lemma_for_row(tp[1], n, bs, tp[3], tp[2], x);
    si::common::read::lemma_for_row(tp[1], n, bs, tp[9], tp[8], x);
    assert(rel[x][0] == Val::Int(skey(m, x)));
    assert(rel[x][3] == Val::Int(snk(m, x)));
    assert(rel[x] == proj(t[x], sd::stored_cols_t1()));
    assert(t[x][0] == rel[x][0]);
    assert(t[x][3] == rel[x][3]);
    assert(proj(t[x], scols()) =~= srow(m, x));
    assert(value_in_column(rel[x][0], sd::stored_columns_t1()[0]));
    assert(value_in_column(rel[x][3], sd::stored_columns_t1()[3]));
}

pub open spec fn su_ok(m: M, db: Database) -> bool {
    &&& frame_ok(m.s_n, m.s_bs, m.s_nb)
    &&& m.s_key_c.len() == m.s_n && m.s_key_b.len() == m.s_nb
    &&& m.s_nk_c.len() == m.s_n && m.s_nk_b.len() == m.s_nb
    &&& m.s_n == db.tables[5].len()
    &&& forall|x: int| 0 <= x < m.s_n ==> #[trigger] proj(db.tables[5][x], scols()) == srow(m, x)
    &&& forall|x: int| 0 <= x < m.s_n ==> in_i64(#[trigger] skey(m, x)) && in_i64(snk(m, x))
    &&& si::common::keyidx::keyidx_ok(m.s_key_c, m.s_key_b, Seq::<u32>::empty(), Seq::<u64>::empty(), m.s_bs, m.s_kind, m.s_n)
}

proof fn lemma_supplier(sv: StoresView, db: Database)
    requires
        si::represents(sv.suppliers, sd::stored_relations(db)),
        db.schema == schema_spec(),
        db_wf(db),
    ensures
        su_ok(model_of(sv), db),
        sv.suppliers[S_S_LAYOUT as int] is U64 && pv_u64(sv.suppliers[S_S_LAYOUT as int]).len() == 2,
        sv.suppliers[S_S_KEY_C as int] is U32 && sv.suppliers[S_S_KEY_B as int] is I64,
        sv.suppliers[S_S_NK_C as int] is U8 && sv.suppliers[S_S_NK_B as int] is I64,
        sv.suppliers[S_S_KIND as int] is U64 && pv_u64(sv.suppliers[S_S_KIND as int]).len() == 1,
{
    let m = model_of(sv);
    let pp = sv.suppliers;
    let rels = sd::stored_relations(db);
    let tp = pp.subrange(13, 30);
    let rel = rels[1];
    let t = db.tables[5];
    lemma_su_cols(tp, rel);
    sd::lemma_stored_relations(db);
    sd::lemma_declared_schema();
    let n = rel.len() as int;
    let bs = sf::u64s(tp[0])[1] as int;
    assert(tp[0] == pp[13] && tp[1] == pp[14] && tp[2] == pp[15] && tp[3] == pp[16] && tp[8] == pp[21] && tp[9] == pp[22]);
    assert(tp[16] == pp[29]);
    assert(pv_u64(pp[13]) == sf::u64s(tp[0]));
    assert(m.s_n == n && m.s_bs == bs);
    assert(su_fields(m, tp));
    assert(m.s_kind == sf::u64s(tp[16])[0]);
    lemma_sgroups(tp[1], n, bs, m.s_nb);
    assert(rel == proj_all(t, sd::stored_cols_t1()));
    assert forall|x: int| 0 <= x < m.s_n implies #[trigger] proj(db.tables[5][x], scols()) == srow(m, x) by {
        lemma_su_row(tp, rel, t, m, x);
    }
    assert forall|x: int| 0 <= x < m.s_n implies in_i64(#[trigger] skey(m, x)) && in_i64(snk(m, x)) by {
        lemma_su_row(tp, rel, t, m, x);
    }
}

// ------------------------------------------------------------------------------------------------ nation

pub open spec fn na_cols(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp[2] is U8 && sf::int_col_at(tp, 1, 2, 3, rel, 0)
    &&& sf::text_col_at(tp, 4, 5, rel, 1)
}

proof fn lemma_na_cols(tp: Seq<PartView>, rel: Seq<Row>)
    requires si::nation_ok(tp, rel),
    ensures na_cols(tp, rel), si::table_layout_ok(tp, rel.len() as int),
{
}

pub open spec fn na_fields(m: M, tp: Seq<PartView>) -> bool {
    &&& m.n_key_c == pv_u8(tp[2]) && m.n_key_b == pv_i64(tp[3])
    &&& m.n_name_o == pv_u64(tp[4]) && m.n_name_y == pv_u8(tp[5])
}

proof fn lemma_na_row(tp: Seq<PartView>, rel: Seq<Row>, t: Seq<Row>, m: M, x: int)
    requires
        na_cols(tp, rel),
        sf::groups_part_ok(tp[1], rel.len() as int, m.n_bs),
        m.n_n == rel.len(),
        na_fields(m, tp),
        rel == proj_all(t, sd::stored_cols_t2()),
        rows_in_columns(rel, sd::stored_columns_t2()),
        0 <= x < m.n_n,
    ensures
        proj(t[x], ncols()) == nrow(m, x),
        in_i64(nkey(m, x)),
{
    let n = m.n_n;
    let bs = m.n_bs;
    lemma_proj_all_index(t, sd::stored_cols_t2());
    si::common::read::lemma_for_row(tp[1], n, bs, tp[3], tp[2], x);
    assert(rel[x][0] == Val::Int(nkey(m, x)));
    assert(rel[x][1] == Val::Text(nname(m, x)));
    assert(rel[x] == proj(t[x], sd::stored_cols_t2()));
    assert(t[x][0] == rel[x][0]);
    assert(t[x][1] == rel[x][1]);
    assert(proj(t[x], ncols()) =~= nrow(m, x));
    assert(value_in_column(rel[x][0], sd::stored_columns_t2()[0]));
}

pub open spec fn na_ok(m: M, db: Database) -> bool {
    &&& frame_ok(m.n_n, m.n_bs, m.n_nb)
    &&& m.n_key_c.len() == m.n_n && m.n_key_b.len() == m.n_nb
    &&& sf::text_parts_wf(m.n_name_o, m.n_name_y, m.n_n)
    &&& m.n_n == db.tables[6].len()
    &&& forall|x: int| 0 <= x < m.n_n ==> #[trigger] proj(db.tables[6][x], ncols()) == nrow(m, x)
    &&& forall|x: int| 0 <= x < m.n_n ==> in_i64(#[trigger] nkey(m, x))
}

proof fn lemma_nation(sv: StoresView, db: Database)
    requires
        si::represents(sv.suppliers, sd::stored_relations(db)),
        db.schema == schema_spec(),
        db_wf(db),
    ensures
        na_ok(model_of(sv), db),
        sv.suppliers[S_N_LAYOUT as int] is U64 && pv_u64(sv.suppliers[S_N_LAYOUT as int]).len() == 2,
        sv.suppliers[S_N_KEY_C as int] is U8 && sv.suppliers[S_N_KEY_B as int] is I64,
        sv.suppliers[S_N_NAME_O as int] is U64 && sv.suppliers[S_N_NAME_Y as int] is U8,
{
    let m = model_of(sv);
    let pp = sv.suppliers;
    let rels = sd::stored_relations(db);
    let tp = pp.subrange(30, 40);
    let rel = rels[2];
    let t = db.tables[6];
    lemma_na_cols(tp, rel);
    sd::lemma_stored_relations(db);
    sd::lemma_declared_schema();
    let n = rel.len() as int;
    let bs = sf::u64s(tp[0])[1] as int;
    assert(tp[0] == pp[30] && tp[1] == pp[31] && tp[2] == pp[32] && tp[3] == pp[33] && tp[4] == pp[34] && tp[5] == pp[35]);
    assert(pv_u64(pp[30]) == sf::u64s(tp[0]));
    assert(m.n_n == n && m.n_bs == bs);
    assert(na_fields(m, tp));
    lemma_sgroups(tp[1], n, bs, m.n_nb);
    assert(rel == proj_all(t, sd::stored_cols_t2()));
    assert(m.n_name_o == sf::u64s(tp[4]) && m.n_name_y == sf::u8s(tp[5]));
    assert forall|x: int| 0 <= x < m.n_n implies #[trigger] proj(db.tables[6][x], ncols()) == nrow(m, x) by {
        lemma_na_row(tp, rel, t, m, x);
    }
    assert forall|x: int| 0 <= x < m.n_n implies in_i64(#[trigger] nkey(m, x)) by {
        lemma_na_row(tp, rel, t, m, x);
    }
}

// ------------------------------------------------------------------------------------------------ primary keys

/// A one-column primary key at the part level: distinct rows of table `ti` (read through the row map `rm` of
/// column 0 values `key`) have distinct keys.
proof fn lemma_pk1(db: Database, ti: int, n: int, rm: Seq<int>, key: spec_fn(int) -> int)
    requires
        db.schema == schema_spec(), db_wf(db), constraints_hold(declared_db(db)),
        0 <= ti < 8,
        db.tables.len() == 8,
        n == db.tables[ti].len(),
        declared_schema()[ti].constraints.len() > 0,
        declared_schema()[ti].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }),
        ff::is_perm(rm, n),
        forall|x: int| 0 <= x < n ==> #[trigger] db.tables[ti][rm[x]][0] == Val::Int(key(x)),
    ensures
        forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] key(a) != #[trigger] key(b),
{
    let ddb = declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies #[trigger] key(a) != #[trigger] key(b) by {
        if key(a) == key(b) {
            let (ia, ib) = (rm[a], rm[b]);
            assert(ia != ib);
            let t = db.tables[ti];
            assert(key_of(t[ia], seq![0nat]) =~= key_of(t[ib], seq![0nat]));
            lemma_row_not_distinct_refl(key_of(t[ia], seq![0nat]));
            assert(ddb.tables[ti] == t);
            lemma_primary_key_identifies(ddb, ti, 0, seq![0nat], true, ia, ib);
        }
    }
}

/// The identity row map.
proof fn lemma_identity(n: int)
    requires n >= 0,
    ensures ff::is_perm(ff::identity_map(n), n), forall|x: int| 0 <= x < n ==> #[trigger] ff::identity_map(n)[x] == x,
{
    ff::lemma_identity_perm(n);
}

/// The partsupp primary key `(ps_partkey, ps_suppkey)` at the part level.
proof fn lemma_ps_pk(m: M, db: Database)
    requires ps_ok(m, db), db.schema == schema_spec(), db_wf(db), constraints_hold(declared_db(db)), db.tables.len() == 8,
    ensures
        forall|a: int, b: int| 0 <= a < m.t_n && 0 <= b < m.t_n && a != b ==>
            #[trigger] tpk(m, a) != #[trigger] tpk(m, b) || tsk(m, a) != tsk(m, b),
{
    let ddb = declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    assert(declared_schema()[4].constraints[0] == (Constraint::Key { cols: seq![0nat, 1nat], primary: true, nulls_distinct: true }));
    assert forall|a: int, b: int| 0 <= a < m.t_n && 0 <= b < m.t_n && a != b implies
        #[trigger] tpk(m, a) != #[trigger] tpk(m, b) || tsk(m, a) != tsk(m, b) by {
        if tpk(m, a) == tpk(m, b) && tsk(m, a) == tsk(m, b) {
            let t = db.tables[4];
            assert(proj(t[a], tcols()) == trow(m, a));
            assert(proj(t[b], tcols()) == trow(m, b));
            assert(proj(t[a], tcols())[0] == t[a][0] && proj(t[a], tcols())[1] == t[a][1]);
            assert(proj(t[b], tcols())[0] == t[b][0] && proj(t[b], tcols())[1] == t[b][1]);
            assert(key_of(t[a], seq![0nat, 1nat]) =~= key_of(t[b], seq![0nat, 1nat]));
            lemma_row_not_distinct_refl(key_of(t[a], seq![0nat, 1nat]));
            assert(ddb.tables[4] == t);
            lemma_primary_key_identifies(ddb, 4, 0, seq![0nat, 1nat], true, a, b);
        }
    }
}

// ------------------------------------------------------------------------------------------------ the model

/// The order position of a key in the stored orders rows is `opos` (orders keys unique).
proof fn lemma_order_pos(orows: Seq<Row>, m: M, k: int)
    requires
        orows.len() == m.o_n,
        forall|q: int| 0 <= q < m.o_n ==> #[trigger] orows[q][0] == Val::Int(okey(m, q)),
        forall|a: int, b: int| 0 <= a < m.o_n && 0 <= b < m.o_n && a != b ==> #[trigger] okey(m, a) != #[trigger] okey(m, b),
    ensures fi::cluster::order_pos(orows, Val::Int(k)) == opos(m, k),
{
    let p = opos(m, k);
    if exists|q: int| 0 <= q < m.o_n && #[trigger] okey(m, q) == k {
        let q0 = choose|q: int| 0 <= q < m.o_n && #[trigger] okey(m, q) == k;
        assert(0 <= p < m.o_n && okey(m, p) == k);
        assert forall|q: int| 0 <= q < orows.len() && q != p implies #[trigger] orows[q][0] != Val::Int(k) by {
            assert(okey(m, q) != okey(m, p));
        }
    } else {
        assert(p == m.o_n);
        assert forall|q: int| 0 <= q < orows.len() && q != p implies #[trigger] orows[q][0] != Val::Int(k) by {
            assert(okey(m, q) != k);
        }
    }
    fi::cluster::lemma_order_pos_at(orows, Val::Int(k), p);
}

/// With the co-clustering flag, the order position of `l_orderkey` never decreases along the stored lineitem rows.
proof fn lemma_cluster(sv: StoresView, db: Database)
    requires
        fi::represents(fx(sv), fd::stored_relations(db)),
        fi::lineitem_rows(fx(sv).subrange(0, 48), fd::stored_relations(db)[0]).len() == model_of(sv).l_n,
        forall|j: int| 0 <= j < model_of(sv).l_n ==>
            #[trigger] fi::lineitem_rows(fx(sv).subrange(0, 48), fd::stored_relations(db)[0])[j][0] == Val::Int(lok(model_of(sv), j)),
        fi::orders_rows(fx(sv).subrange(48, 74), fd::stored_relations(db)[1]).len() == model_of(sv).o_n,
        forall|q: int| 0 <= q < model_of(sv).o_n ==>
            #[trigger] fi::orders_rows(fx(sv).subrange(48, 74), fd::stored_relations(db)[1])[q][0] == Val::Int(okey(model_of(sv), q)),
        forall|a: int, b: int| 0 <= a < model_of(sv).o_n && 0 <= b < model_of(sv).o_n && a != b ==>
            #[trigger] okey(model_of(sv), a) != #[trigger] okey(model_of(sv), b),
    ensures
        model_of(sv).cluster == 1 ==> forall|a: int, b: int| 0 <= a <= b < model_of(sv).l_n ==>
            #[trigger] opos(model_of(sv), lok(model_of(sv), a)) <= #[trigger] opos(model_of(sv), lok(model_of(sv), b)),
{
    let m = model_of(sv);
    let rels = fd::stored_relations(db);
    let lrows = fi::lineitem_rows(fx(sv).subrange(0, 48), rels[0]);
    let orows = fi::orders_rows(fx(sv).subrange(48, 74), rels[1]);
    if m.cluster == 1 {
        assert(fx(sv).subrange(0, 48) == fx(sv).subrange(fi::LINEITEM_FIRST as int, (fi::LINEITEM_FIRST + fi::LI_PARTS) as int));
        assert(fx(sv).subrange(48, 74) == fx(sv).subrange(fi::ORDERS_FIRST as int, (fi::ORDERS_FIRST + fi::OR_PARTS) as int));
        assert(fi::cluster::clustered(lrows, orows));
        assert forall|a: int, b: int| 0 <= a <= b < m.l_n implies
            #[trigger] opos(m, lok(m, a)) <= #[trigger] opos(m, lok(m, b)) by {
            fi::cluster::lemma_clustered_le(lrows, orows, a, b);
            lemma_order_pos(orows, m, lok(m, a));
            lemma_order_pos(orows, m, lok(m, b));
        }
    }
}

/// partsig's stored relations are custpart's (the same declaration).
proof fn lemma_same_relations_sig(db: Database)
    ensures gd::stored_relations(db) == cd::stored_relations(db),
{
    assert(gd::stored_cols_t0() =~= cd::stored_cols_t0());
    assert(gd::stored_cols_t1() =~= cd::stored_cols_t1());
    assert(gd::stored_relations(db) =~= cd::stored_relations(db));
}

/// partsig's signatures cover the model's part names (custpart's; both storages hold the same part relation).
proof fn lemma_psig(sv: StoresView, db: Database)
    requires
        ci::represents(sv.custpart, cd::stored_relations(db)),
        gi::represents(sv.partsig, gd::stored_relations(db)),
    ensures
        psig_ok(sigs_of(sv), model_of(sv)),
        sv.partsig.len() == 51 && sv.partsig[G_SIG as int] is U64,
{
    let m = model_of(sv);
    lemma_same_relations_sig(db);
    let rels = cd::stored_relations(db);
    let g = sv.partsig;
    let gc = g.subrange(0, 50);
    assert(ci::represents(gc, rels));
    let tp1 = sv.custpart.subrange(21, 50);
    let tp2 = gc.subrange(21, 50);
    assert(ci::part_ok(tp1, rels[1]));
    assert(ci::part_ok(tp2, rels[1]));
    lemma_pa_cols(tp1, rels[1]);
    lemma_pa_cols(tp2, rels[1]);
    let rel = rels[1];
    assert(tp1[0] == sv.custpart[21] && tp1[4] == sv.custpart[25] && tp1[5] == sv.custpart[26]);
    assert(tp2[0] == g[21] && tp2[4] == g[25] && tp2[5] == g[26]);
    assert(m.p_n == rel.len()) by {
        assert(ci::table_layout_ok(tp1, rel.len() as int));
    }
    assert(gi::part_rows(g) == rel.len()) by {
        assert(ci::table_layout_ok(tp2, rel.len() as int));
    }
    assert(gi::sig_ok(g));
    assert(sigs_of(sv) == gi::sigs(g));
    assert forall|c: int| 0 <= c < m.p_n implies #[trigger] gi::sig_row_ok(pname(m, c), sigs_of(sv)[c]) by {
        assert(cf::text_col(rel, 1, cf::u64s(tp1[4]), cf::u8s(tp1[5])));
        assert(cf::text_col(rel, 1, cf::u64s(tp2[4]), cf::u8s(tp2[5])));
        assert(rel[c][1] == Val::Text(cf::text_of(cf::u64s(tp1[4]), cf::u8s(tp1[5]), c)));
        assert(rel[c][1] == Val::Text(cf::text_of(cf::u64s(tp2[4]), cf::u8s(tp2[5]), c)));
        assert(m.p_name_o == cf::u64s(tp1[4]) && m.p_name_y == cf::u8s(tp1[5]));
        assert(pname(m, c) == cf::text_of(cf::u64s(tp1[4]), cf::u8s(tp1[5]), c));
        assert(gi::pname_of(g, c) == cf::text_of(cf::u64s(tp2[4]), cf::u8s(tp2[5]), c));
        assert(gi::sig_row_ok(gi::pname_of(g, c), gi::sigs(g)[c]));
    }
}

/// Every database bound to the parts gives the model facts and reads its tables through the model.
/// factspk's stored relations are facts' (the same declaration).
proof fn lemma_same_relations(db: Database)
    ensures kd::stored_relations(db) == fd::stored_relations(db),
{
    assert(kd::stored_cols_t0() =~= fd::stored_cols_t0());
    assert(kd::stored_cols_t1() =~= fd::stored_cols_t1());
    assert(kd::stored_relations(db) =~= fd::stored_relations(db));
}

/// factspk's directory and facts' l_partkey key index, read through the model.
proof fn lemma_pdir(sv: StoresView, db: Database)
    requires
        ki::represents(sv.factspk, kd::stored_relations(db)),
        fi::represents(fx(sv), fd::stored_relations(db)),
        li_ok(model_of(sv), db),
        db.tables.len() == 8,
        fd::stored_relations(db)[0].len() == db.tables[0].len(),
    ensures
        pdir_ok(model_of(sv)),
{
    let m = model_of(sv);
    let f = fx(sv);
    let pk = sv.factspk;
    let rels = fd::stored_relations(db);
    let tp = f.subrange(0, 48);
    assert(f.subrange(fi::LINEITEM_FIRST as int, (fi::LINEITEM_FIRST + fi::LI_PARTS) as int) == tp);
    assert(fi::lineitem_ok(tp, rels[0]));
    let rows = fi::lineitem_rows(tp, rels[0]);
    assert(fi::lineitem_cols_ok(tp, rows));
    assert(tp[0] == pk[0] && tp[6] == pk[6] && tp[7] == pk[7]);
    assert(tp[45] == pk[45] && tp[46] == pk[46] && tp[47] == pk[47]);
    assert(m.l_pk_c == ff::u32s(tp[6]) && m.l_pk_b == ff::i64s(tp[7]));
    assert(m.l_ic == ff::u32s(tp[45]) && m.l_ib == ff::u64s(tp[46]) && m.l_kind == ff::u64s(tp[47])[0]);
    assert(m.l_bs == ff::u64s(tp[0])[1] as int);
    assert(rows.len() == m.l_n);
    assert(fi::common::keyidx::keyidx_ok(m.l_pk_c, m.l_pk_b, m.l_ic, m.l_ib, m.l_bs, m.l_kind, m.l_n));
    assert(ki::dir_ok(pk));
    assert(m.dir == ki::dir_of(pk));
    assert(m.kb == ki::kb_of(pk));
    assert(ki::li_rows(pk) == m.l_n);
    assert forall|r: int| #[trigger] ki::key_at(pk, r) == lkey(m, r) by {}
    assert forall|i: int| 0 <= i < m.dir.len() implies #[trigger] dentry(m, i) by {
        assert(ki::dir_entry_ok(pk, i));
        let d = m.dir[i] as int;
        assert forall|r: int| 0 <= r < d implies #[trigger] lkey(m, r) < m.kb + i by {
            assert(ki::key_at(pk, r) < ki::kb_of(pk) + i);
        }
        if d < m.l_n {
            assert(ki::key_at(pk, d) >= ki::kb_of(pk) + i);
        }
    }
}

pub proof fn lemma_model(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        model_ok(model_of(sv)),
        ofacts_ok(model_of(sv)),
        rel_ok(model_of(sv), db),
        kinds_ok(sv),
        pdir_ok(model_of(sv)),
        psig_ok(sigs_of(sv), model_of(sv)),
{
    let m = model_of(sv);
    assert(crate::gendb_entry::stores::stored_ok(sv, db));
    lemma_psig(sv, db);
    lemma_same_relations(db);
    assert(ki::represents(sv.factspk, kd::stored_relations(db)));
    assert(sv.factspk.subrange(0, ki::FACTS_PARTS as int) == fx(sv));
    assert(fi::represents(fx(sv), fd::stored_relations(db)));
    lemma_lineitem(sv, db);
    lemma_orders(sv, db);
    lemma_part(sv, db);
    lemma_partsupp(sv, db);
    lemma_supplier(sv, db);
    lemma_nation(sv, db);
    crate::gendb_constraints::lemma_declared_schema();
    // orders: o_orderkey through the row map
    assert forall|q: int| 0 <= q < m.o_n implies #[trigger] db.tables[1][m.o_map[q]][0] == Val::Int((|x: int| okey(m, x))(q)) by {
        assert(proj(db.tables[1][m.o_map[q]], ocols()) == orow(m, q));
        assert(proj(db.tables[1][m.o_map[q]], ocols())[0] == db.tables[1][m.o_map[q]][0]);
    }
    lemma_pk1(db, 1, m.o_n, m.o_map, |x: int| okey(m, x));
    lemma_identity(m.p_n);
    assert forall|c: int| 0 <= c < m.p_n implies #[trigger] db.tables[3][ff::identity_map(m.p_n)[c]][0] == Val::Int((|x: int| pkey(m, x))(c)) by {
        assert(proj(db.tables[3][c], pcols()) == prow(m, c));
        assert(proj(db.tables[3][c], pcols())[0] == db.tables[3][c][0]);
    }
    lemma_pk1(db, 3, m.p_n, ff::identity_map(m.p_n), |x: int| pkey(m, x));
    lemma_identity(m.s_n);
    assert forall|s: int| 0 <= s < m.s_n implies #[trigger] db.tables[5][ff::identity_map(m.s_n)[s]][0] == Val::Int((|x: int| skey(m, x))(s)) by {
        assert(proj(db.tables[5][s], scols()) == srow(m, s));
        assert(proj(db.tables[5][s], scols())[0] == db.tables[5][s][0]);
    }
    lemma_pk1(db, 5, m.s_n, ff::identity_map(m.s_n), |x: int| skey(m, x));
    lemma_identity(m.n_n);
    assert forall|n: int| 0 <= n < m.n_n implies #[trigger] db.tables[6][ff::identity_map(m.n_n)[n]][0] == Val::Int((|x: int| nkey(m, x))(n)) by {
        assert(proj(db.tables[6][n], ncols()) == nrow(m, n));
        assert(proj(db.tables[6][n], ncols())[0] == db.tables[6][n][0]);
    }
    lemma_pk1(db, 6, m.n_n, ff::identity_map(m.n_n), |x: int| nkey(m, x));
    lemma_ps_pk(m, db);
    assert(keys_ok(m)) by {
        assert forall|a: int, b: int| 0 <= a < m.o_n && 0 <= b < m.o_n && a != b implies #[trigger] okey(m, a) != #[trigger] okey(m, b) by {
            assert((|x: int| okey(m, x))(a) != (|x: int| okey(m, x))(b));
        }
        assert forall|a: int, b: int| 0 <= a < m.p_n && 0 <= b < m.p_n && a != b implies #[trigger] pkey(m, a) != #[trigger] pkey(m, b) by {
            assert((|x: int| pkey(m, x))(a) != (|x: int| pkey(m, x))(b));
        }
        assert forall|a: int, b: int| 0 <= a < m.s_n && 0 <= b < m.s_n && a != b implies #[trigger] skey(m, a) != #[trigger] skey(m, b) by {
            assert((|x: int| skey(m, x))(a) != (|x: int| skey(m, x))(b));
        }
        assert forall|a: int, b: int| 0 <= a < m.n_n && 0 <= b < m.n_n && a != b implies #[trigger] nkey(m, a) != #[trigger] nkey(m, b) by {
            assert((|x: int| nkey(m, x))(a) != (|x: int| nkey(m, x))(b));
        }
    }
    assert(rel_ok(m, db));
    assert(shapes_ok(m));
    assert(values_ok(m));
    lemma_cluster(sv, db);
    assert(ofacts_ok(m));
    fd::lemma_stored_relations(db);
    lemma_pdir(sv, db);
    assert(ki::dir_ok(sv.factspk));
    assert(kinds_ok(sv));
}

} // verus!
