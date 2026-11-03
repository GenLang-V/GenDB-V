//! What a database bound to the stored parts (`gendb_entry::bound_db`) gives the scan and the proof.
//!
//! - lineitem (storage `facts`, clustered): the stored rows' query columns `model::li_rows` are the database's
//!   lineitem rows projected on `[l_partkey, l_extendedprice, l_discount, l_shipdate]` under the stored row map, a
//!   permutation (`lemma_li_link`); the parts have the shape the scan reads (`model::li_shape`).
//! - part (storage `custpart`, canonical order): `model::pa_rows` are the part rows projected on
//!   `[p_partkey, p_type]` in order (`lemma_pa_link`); the parts have the shape of `model::pa_shape`, with distinct
//!   keys from the declared primary key of part.
//! - every row of `lineitem x part` has the typed values the condition and the arguments read
//!   (`sqlrow::prow_typed`, `lemma_rows_typed`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::numeric::*;
use crate::spec::constraints::{constraints_hold, key_of};
use crate::link::expr::{ival, tval};
use crate::link::query::{proj, proj_all};
use crate::link::source::lemma_proj_all_index;
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::gendb_entry::bound_db;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::part_len;
use crate::gendb_entry::stores::{StoresView, stored_ok};
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::facts::declaration as fd;
use crate::stores::custpart::interface as cpi;
use crate::stores::custpart::interface::common::colfmt as cpc;
use crate::stores::custpart::interface::common::keyidx as cpk;
use crate::stores::custpart::declaration as cpd;
use super::model::*;
use super::sqlrow::{num2, p15i, prow_typed};

verus! {

// ------------------------------------------------------------------------------------------------ typing

/// The lineitem query columns of a row: 16 columns, l_partkey an integer, price and discount numeric(15, 2),
/// shipdate a date.
pub open spec fn lrow_typed(r: Row) -> bool {
    &&& r.len() == 16
    &&& r[1] == Val::Int(ival(r[1]))
    &&& num2(r[5]) && num2(r[6])
    &&& r[10] == Val::Date(ival(r[10]))
}

/// The part query columns of a row: 9 columns, p_partkey an integer, p_type a text.
pub open spec fn prow9_typed(r: Row) -> bool {
    &&& r.len() == 9
    &&& r[0] == Val::Int(ival(r[0]))
    &&& r[4] == Val::Text(tval(r[4]))
}

pub proof fn lemma_pow10_15()
    ensures pow10(15) == p15i(),
{
    assert(pow10(15) == p15i()) by (compute);
}

/// The lineitem and part rows of a database of the schema are typed.
pub proof fn lemma_rows_typed(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures
        db.tables.len() == 8,
        forall|i: int| 0 <= i < db.tables[0].len() ==> lrow_typed(#[trigger] db.tables[0][i]),
        forall|i: int| 0 <= i < db.tables[3].len() ==> prow9_typed(#[trigger] db.tables[3][i]),
{
    fd::lemma_declared_schema();
    cpd::lemma_declared_schema();
    lemma_pow10_15();
    let int8 = Column { ty: SqlType::Int8, nullable: false };
    let num = Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false };
    let date = Column { ty: SqlType::Date, nullable: false };
    let text = Column { ty: SqlType::Text, nullable: false };
    assert(schema_spec()[0].columns.len() == 16) by (compute);
    assert(schema_spec()[0].columns[1] == int8) by (compute);
    assert(schema_spec()[0].columns[5] == num) by (compute);
    assert(schema_spec()[0].columns[6] == num) by (compute);
    assert(schema_spec()[0].columns[10] == date) by (compute);
    assert(schema_spec()[3].columns.len() == 9) by (compute);
    assert(schema_spec()[3].columns[0] == int8) by (compute);
    assert(schema_spec()[3].columns[4] == text) by (compute);
    assert forall|i: int| 0 <= i < db.tables[0].len() implies lrow_typed(#[trigger] db.tables[0][i]) by {
        let r = db.tables[0][i];
        assert(row_in_table(r, db.schema[0]));
        assert(value_in_column(r[1], int8));
        assert(value_in_column(r[5], num));
        assert(value_in_column(r[6], num));
        assert(value_in_column(r[10], date));
    }
    assert forall|i: int| 0 <= i < db.tables[3].len() implies prow9_typed(#[trigger] db.tables[3][i]) by {
        let r = db.tables[3][i];
        assert(row_in_table(r, db.schema[3]));
        assert(value_in_column(r[0], int8));
        assert(value_in_column(r[4], text));
    }
}

/// A product row of a typed lineitem row and a typed part row is typed.
pub proof fn lemma_prow_typed(l: Row, p: Row)
    requires lrow_typed(l), prow9_typed(p),
    ensures prow_typed(l + p),
{
    let x = l + p;
    assert(x[1] == l[1] && x[5] == l[5] && x[6] == l[6] && x[10] == l[10]);
    assert(x[16] == p[0] && x[20] == p[4]);
}

// ------------------------------------------------------------------------------------------------ part

/// The parts of table part in storage custpart.
pub open spec fn pa_tp(cp: Seq<PartView>) -> Seq<PartView> {
    cp.subrange(cpi::PART_FIRST as int, (cpi::PART_FIRST + cpi::PA_PARTS) as int)
}

/// Projecting rows of `w` values on the columns `0, 1, ..., w - 1` keeps them.
pub proof fn lemma_proj_full(rows: Seq<Row>, cols: Seq<nat>, w: nat)
    requires
        cols.len() == w,
        forall|k: int| 0 <= k < w ==> #[trigger] cols[k] == k,
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() == w,
    ensures proj_all(rows, cols) == rows,
{
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] proj_all(rows, cols)[i] == rows[i] by {
        assert(proj(rows[i], cols) =~= rows[i]);
    }
    assert(proj_all(rows, cols) =~= rows);
}

/// A declared primary key on column 0 identifies the row.
pub proof fn lemma_pk0(db: Database, t: int)
    requires
        constraints_hold(declared_db(db)),
        db.tables.len() == 8,
        0 <= t < 8,
        declared_schema()[t].constraints.len() > 0,
        declared_schema()[t].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }),
        forall|i: int| 0 <= i < db.tables[t].len() ==> (#[trigger] db.tables[t][i]).len() > 0,
    ensures
        forall|i: int, j: int| 0 <= i < db.tables[t].len() && 0 <= j < db.tables[t].len()
            && #[trigger] db.tables[t][i][0] == #[trigger] db.tables[t][j][0] ==> i == j,
{
    crate::gendb_constraints::lemma_declared_schema();
    let rows = db.tables[t];
    let ddb = declared_db(db);
    assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && #[trigger] rows[i][0] == #[trigger] rows[j][0]
        implies i == j by {
        assert(key_of(rows[i], seq![0nat]) =~= key_of(rows[j], seq![0nat]));
        crate::bridge::equality::lemma_row_not_distinct_refl(key_of(rows[i], seq![0nat]));
        crate::bridge::constraints::lemma_primary_key_identifies(ddb, t, 0, seq![0nat], true, i, j);
    }
}

/// The part parts in the custpart parts.
pub proof fn lemma_pa_tp(cp: Seq<PartView>)
    requires cp.len() == cpi::CUSTPART_PARTS,
    ensures forall|k: int| 0 <= k < cpi::PA_PARTS ==> #[trigger] pa_tp(cp)[k] == cp[pp(k as usize)],
{
}

/// The part column facts of `part_ok` that the lookups read: shapes, keys, types and the key order flag.
pub proof fn lemma_pa_cols(cp: Seq<PartView>, rel: Seq<Row>)
    requires
        cp.len() == cpi::CUSTPART_PARTS,
        cpi::part_ok(pa_tp(cp), rel),
    ensures
        n_pa(cp) == rel.len(),
        cp[pp(cpi::PA_LAYOUT)] is U64 && cpc::u64s(cp[pp(cpi::PA_LAYOUT)]).len() == 2,
        cpc::groups_part_ok(cp[pp(cpi::PA_GROUPS)], n_pa(cp), pa_bsize(cp)),
        cp[pp(cpi::PA_PARTKEY_CODES)] is U32,
        cp[pp(cpi::PA_PARTKEY_BASE)] is I64 && part_len(cp[pp(cpi::PA_PARTKEY_BASE)]) == pa_gs(cp).len() - 1,
        cp[pp(cpi::PA_TYPE_CODES)] is U8 && part_len(cp[pp(cpi::PA_TYPE_CODES)]) == n_pa(cp),
        cp[pp(cpi::PA_TYPE_BASE)] is U64 && part_len(cp[pp(cpi::PA_TYPE_BASE)]) == pa_gs(cp).len() - 1,
        cp[pp(cpi::PA_TYPE_DICT_OFFS)] is U64 && cp[pp(cpi::PA_TYPE_DICT_BYTES)] is U8,
        td_o(cp).len() >= 1,
        cpc::text_parts_wf(td_o(cp), td_y(cp), n_td(cp)),
        forall|j: int| 0 <= j < n_pa(cp) ==> 0 <= #[trigger] tidx_at(cp, j) < n_td(cp),
        forall|j: int| 0 <= j < n_pa(cp) ==> #[trigger] rel[j][0] == Val::Int(pkey_at(cp, j)),
        forall|j: int| 0 <= j < n_pa(cp) ==> #[trigger] rel[j][4] == Val::Text(ptype_at(cp, j)),
        cp[pp(cpi::PA_KEYIDX_KIND)] is U64 && cpc::u64s(cp[pp(cpi::PA_KEYIDX_KIND)]).len() == 1,
        cpk::keyidx_ok(cpc::u32s(cp[pp(cpi::PA_PARTKEY_CODES)]), cpc::i64s(cp[pp(cpi::PA_PARTKEY_BASE)]), Seq::<u32>::empty(),
            Seq::<u64>::empty(), pa_bsize(cp), cpc::u64s(cp[pp(cpi::PA_KEYIDX_KIND)])[0], n_pa(cp)),
{
    hide(cpc::text_col_at);
    let tp = pa_tp(cp);
    lemma_pa_tp(cp);
    assert(tp[cpi::PA_PARTKEY_CODES as int] == cp[pp(cpi::PA_PARTKEY_CODES)]);
    assert(tp[cpi::PA_PARTKEY_BASE as int] == cp[pp(cpi::PA_PARTKEY_BASE)]);
    assert(tp[cpi::PA_TYPE_CODES as int] == cp[pp(cpi::PA_TYPE_CODES)]);
    assert(tp[cpi::PA_TYPE_BASE as int] == cp[pp(cpi::PA_TYPE_BASE)]);
    assert(tp[cpi::PA_TYPE_DICT_OFFS as int] == cp[pp(cpi::PA_TYPE_DICT_OFFS)]);
    assert(tp[cpi::PA_TYPE_DICT_BYTES as int] == cp[pp(cpi::PA_TYPE_DICT_BYTES)]);
    assert(tp[cpi::PA_GROUPS as int] == cp[pp(cpi::PA_GROUPS)]);
    assert(tp[cpi::PA_LAYOUT as int] == cp[pp(cpi::PA_LAYOUT)]);
    assert(tp[cpi::PA_KEYIDX_KIND as int] == cp[pp(cpi::PA_KEYIDX_KIND)]);
    let n = rel.len() as int;
    let bs = cpc::u64s(tp[cpi::PA_LAYOUT as int])[1] as int;
    cpc::lemma_uniform_groups(tp[cpi::PA_GROUPS as int], n, bs);
    assert forall|j: int| 0 <= j < n_pa(cp) implies 0 <= #[trigger] tidx_at(cp, j) < n_td(cp) by {
        assert(rel[j][4] == Val::Text(ptype_at(cp, j)));
    }
}

/// Sorted keys under the key index kind 1.
pub proof fn lemma_pa_sorted(cp: Seq<PartView>)
    requires
        cp[pp(cpi::PA_PARTKEY_CODES)] is U32,
        cp[pp(cpi::PA_PARTKEY_BASE)] is I64,
        cpc::groups_part_ok(cp[pp(cpi::PA_GROUPS)], n_pa(cp), pa_bsize(cp)),
        cpk::keyidx_ok(cpc::u32s(cp[pp(cpi::PA_PARTKEY_CODES)]), cpc::i64s(cp[pp(cpi::PA_PARTKEY_BASE)]), Seq::<u32>::empty(),
            Seq::<u64>::empty(), pa_bsize(cp), cpc::u64s(cp[pp(cpi::PA_KEYIDX_KIND)])[0], n_pa(cp)),
    ensures
        cpc::u64s(cp[pp(cpi::PA_KEYIDX_KIND)])[0] == 1 ==> forall|j: int| 0 <= j < n_pa(cp) - 1 ==> #[trigger] pkey_at(cp, j) <= pkey_at(cp, j + 1),
{
    let n = n_pa(cp);
    let bs = pa_bsize(cp);
    let kc = cpc::u32s(cp[pp(cpi::PA_PARTKEY_CODES)]);
    let kb = cpc::i64s(cp[pp(cpi::PA_PARTKEY_BASE)]);
    let kind = cpc::u64s(cp[pp(cpi::PA_KEYIDX_KIND)])[0];
    if kind == 1 {
        assert forall|j: int| 0 <= j < n - 1 implies #[trigger] pkey_at(cp, j) <= pkey_at(cp, j + 1) by {
            assert(cpk::sorted_at(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), bs, kind, j));
            cpk::lemma_fkey_for_at(cp[pp(cpi::PA_GROUPS)], n, bs, cp[pp(cpi::PA_PARTKEY_BASE)], cp[pp(cpi::PA_PARTKEY_CODES)], j);
            cpk::lemma_fkey_for_at(cp[pp(cpi::PA_GROUPS)], n, bs, cp[pp(cpi::PA_PARTKEY_BASE)], cp[pp(cpi::PA_PARTKEY_CODES)], j + 1);
        }
    }
}

/// Distinct keys from the primary key of part.
pub proof fn lemma_pa_distinct(db: Database, cp: Seq<PartView>)
    requires
        constraints_hold(declared_db(db)),
        db.tables.len() == 8,
        forall|i: int| 0 <= i < db.tables[3].len() ==> prow9_typed(#[trigger] db.tables[3][i]),
        n_pa(cp) == db.tables[3].len(),
        forall|j: int| 0 <= j < n_pa(cp) ==> #[trigger] db.tables[3][j][0] == Val::Int(pkey_at(cp, j)),
    ensures
        forall|a: int, b: int| 0 <= a < n_pa(cp) && 0 <= b < n_pa(cp) && a != b ==> #[trigger] pkey_at(cp, a) != #[trigger] pkey_at(cp, b),
{
    let rel = db.tables[3];
    let n = n_pa(cp);
    crate::gendb_constraints::lemma_declared_schema();
    assert(declared_schema()[3].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert forall|i: int| 0 <= i < rel.len() implies (#[trigger] rel[i]).len() > 0 by {
        assert(prow9_typed(rel[i]));
    }
    lemma_pk0(db, 3);
    assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies #[trigger] pkey_at(cp, a) != #[trigger] pkey_at(cp, b) by {
        if pkey_at(cp, a) == pkey_at(cp, b) {
            assert(rel[a][0] == Val::Int(pkey_at(cp, a)));
            assert(rel[b][0] == Val::Int(pkey_at(cp, b)));
            assert(rel[a][0] == rel[b][0]);
        }
    }
}

/// The stored part rows are the part rows projected on `[p_partkey, p_type]`.
pub proof fn lemma_pa_rows(cp: Seq<PartView>, rel: Seq<Row>)
    requires
        n_pa(cp) == rel.len(),
        forall|j: int| 0 <= j < n_pa(cp) ==> #[trigger] rel[j][0] == Val::Int(pkey_at(cp, j)),
        forall|j: int| 0 <= j < n_pa(cp) ==> #[trigger] rel[j][4] == Val::Text(ptype_at(cp, j)),
    ensures
        pa_rows(cp) == proj_all(rel, seq![0nat, 4nat]),
{
    let n = rel.len() as int;
    lemma_proj_all_index(rel, seq![0nat, 4nat]);
    assert forall|j: int| 0 <= j < n implies #[trigger] pa_rows(cp)[j] == proj_all(rel, seq![0nat, 4nat])[j] by {
        assert(rel[j][0] == Val::Int(pkey_at(cp, j)));
        assert(rel[j][4] == Val::Text(ptype_at(cp, j)));
        assert(proj(rel[j], seq![0nat, 4nat]) =~= pa_row(pkey_at(cp, j), ptype_at(cp, j)));
    }
    assert(pa_rows(cp) =~= proj_all(rel, seq![0nat, 4nat]));
}

/// For a bound database: the part parts have the shape of `pa_shape`, and the stored part rows are the part rows
/// projected on `[p_partkey, p_type]`.
pub proof fn lemma_pa_link(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        pa_shape(sv.custpart),
        n_pa(sv.custpart) == db.tables[3].len(),
        pa_rows(sv.custpart) == proj_all(db.tables[3], seq![0nat, 4nat]),
{
    hide(cpi::customer_ok);
    hide(cpi::part_ok);
    let cp = sv.custpart;
    let rel = db.tables[3];
    let rels = cpd::stored_relations(db);
    lemma_rows_typed(db);
    cpd::lemma_declared_schema();
    assert(stored_ok(sv, db));
    assert(cpi::represents(cp, rels));
    lemma_proj_full(rel, cpd::stored_cols_t1(), 9);
    assert(rels[1] == rel);
    assert(cpi::part_ok(pa_tp(cp), rel));
    lemma_pa_cols(cp, rel);
    lemma_pa_sorted(cp);
    lemma_pa_distinct(db, cp);
    lemma_pa_rows(cp, rel);
}

// ------------------------------------------------------------------------------------------------ lineitem

/// The parts of table lineitem in storage facts.
pub open spec fn li_tp(fp: Seq<PartView>) -> Seq<PartView> {
    fp.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int)
}

/// Columns of the lineitem query values.
pub open spec fn ca() -> Seq<nat> {
    seq![1nat, 5nat, 6nat, 10nat]
}

/// The facts of `represents` about the lineitem parts that the scan reads.
pub proof fn lemma_li_facts(fp: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires represents(fp, rels),
    ensures ({
        let tp = li_tp(fp);
        let n = rels[0].len() as int;
        let srows = lineitem_rows(tp, rels[0]);
        &&& fp.len() == FACTS_PARTS
        &&& table_layout_ok(tp, n)
        &&& is_perm(lineitem_map(tp, n), n)
        &&& tp[LI_PARTKEY_CODES as int] is U32
        &&& int_col_at(tp, LI_GROUPS as int, LI_PARTKEY_CODES as int, LI_PARTKEY_BASE as int, srows, 1)
        &&& tp[LI_EXTENDEDPRICE_CODES as int] is U32
        &&& num_col_at(tp, LI_GROUPS as int, LI_EXTENDEDPRICE_CODES as int, LI_EXTENDEDPRICE_BASE as int, srows, 5, 2)
        &&& tp[LI_DISCOUNT_CODES as int] is U8
        &&& num_col_at(tp, LI_GROUPS as int, LI_DISCOUNT_CODES as int, LI_DISCOUNT_BASE as int, srows, 6, 2)
        &&& tp[LI_SHIPDATE_CODES as int] is U16
        &&& date_col_at(tp, LI_GROUPS as int, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, srows, 10)
        &&& zone_at(tp, LI_GROUPS as int, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, LI_SHIPDATE_ZMAX as int)
    }),
{
}

/// The query columns of one stored lineitem row.
pub proof fn lemma_stored_row_cols(fp: Seq<PartView>, srows: Seq<Row>, j: int)
    requires
        fp.len() == FACTS_PARTS,
        0 <= j < srows.len(),
        ({
            let tp = li_tp(fp);
            &&& int_col_at(tp, LI_GROUPS as int, LI_PARTKEY_CODES as int, LI_PARTKEY_BASE as int, srows, 1)
            &&& num_col_at(tp, LI_GROUPS as int, LI_EXTENDEDPRICE_CODES as int, LI_EXTENDEDPRICE_BASE as int, srows, 5, 2)
            &&& num_col_at(tp, LI_GROUPS as int, LI_DISCOUNT_CODES as int, LI_DISCOUNT_BASE as int, srows, 6, 2)
            &&& date_col_at(tp, LI_GROUPS as int, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, srows, 10)
        }),
    ensures
        srows[j][1] == Val::Int(lpk_at(fp, j)),
        srows[j][5] == (Val::Num { coeff: price_at(fp, j), scale: 2 }),
        srows[j][6] == (Val::Num { coeff: disc_at(fp, j), scale: 2 }),
        srows[j][10] == Val::Date(ship_at(fp, j)),
{
    let tp = li_tp(fp);
    assert(tp[LI_GROUPS as int] == fp[LI_GROUPS as int]);
    assert(tp[LI_PARTKEY_CODES as int] == fp[LI_PARTKEY_CODES as int]);
    assert(tp[LI_PARTKEY_BASE as int] == fp[LI_PARTKEY_BASE as int]);
    assert(tp[LI_EXTENDEDPRICE_CODES as int] == fp[LI_EXTENDEDPRICE_CODES as int]);
    assert(tp[LI_EXTENDEDPRICE_BASE as int] == fp[LI_EXTENDEDPRICE_BASE as int]);
    assert(tp[LI_DISCOUNT_CODES as int] == fp[LI_DISCOUNT_CODES as int]);
    assert(tp[LI_DISCOUNT_BASE as int] == fp[LI_DISCOUNT_BASE as int]);
    assert(tp[LI_SHIPDATE_CODES as int] == fp[LI_SHIPDATE_CODES as int]);
    assert(tp[LI_SHIPDATE_BASE as int] == fp[LI_SHIPDATE_BASE as int]);
}

/// The shape facts of the lineitem parts, from `represents` (without the value bounds).
pub proof fn lemma_li_shape_parts(fp: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires represents(fp, rels),
    ensures
        n_li(fp) == rels[0].len(),
        fp.len() == FACTS_PARTS,
        fp[LI_GROUPS as int] is U64,
        groups_wf(li_gs(fp), n_li(fp)),
        fp[LI_SHIPDATE_CODES as int] is U16,
        fp[LI_PARTKEY_CODES as int] is U32 && part_len(fp[LI_PARTKEY_CODES as int]) == n_li(fp),
        fp[LI_EXTENDEDPRICE_CODES as int] is U32 && part_len(fp[LI_EXTENDEDPRICE_CODES as int]) == n_li(fp),
        fp[LI_DISCOUNT_CODES as int] is U8 && part_len(fp[LI_DISCOUNT_CODES as int]) == n_li(fp),
        li_group_part(fp, LI_SHIPDATE_BASE as int),
        li_group_part(fp, LI_SHIPDATE_ZMAX as int),
        li_group_part(fp, LI_PARTKEY_BASE as int),
        li_group_part(fp, LI_EXTENDEDPRICE_BASE as int),
        li_group_part(fp, LI_DISCOUNT_BASE as int),
        zone_max_ok(li_gs(fp), fp[LI_SHIPDATE_BASE as int], fp[LI_SHIPDATE_CODES as int], i64s(fp[LI_SHIPDATE_ZMAX as int])),
{
    hide(represents);
    lemma_li_facts(fp, rels);
    let tp = li_tp(fp);
    let n = rels[0].len() as int;
    assert forall|k: int| 0 <= k < 48 implies #[trigger] tp[k] == fp[k] by {}
    let bs = u64s(tp[LI_LAYOUT as int])[1] as int;
    lemma_uniform_groups(tp[LI_GROUPS as int], n, bs);
    assert(li_gs(fp) == gs_at(tp, LI_GROUPS as int));
    assert(tp[LI_SHIPDATE_CODES as int] == fp[LI_SHIPDATE_CODES as int]);
    assert(n_li(fp) == n);
    assert(tp[LI_SHIPDATE_ZMAX as int] == fp[LI_SHIPDATE_ZMAX as int]);
    assert(tp[LI_SHIPDATE_BASE as int] == fp[LI_SHIPDATE_BASE as int]);
    assert(tp[LI_PARTKEY_BASE as int] == fp[LI_PARTKEY_BASE as int]);
    assert(tp[LI_DISCOUNT_BASE as int] == fp[LI_DISCOUNT_BASE as int]);
    assert(tp[LI_EXTENDEDPRICE_BASE as int] == fp[LI_EXTENDEDPRICE_BASE as int]);
    assert(tp[LI_DISCOUNT_CODES as int] == fp[LI_DISCOUNT_CODES as int]);
    assert(tp[LI_PARTKEY_CODES as int] == fp[LI_PARTKEY_CODES as int]);
    assert(tp[LI_EXTENDEDPRICE_CODES as int] == fp[LI_EXTENDEDPRICE_CODES as int]);
}

/// One stored lineitem row's query columns are its database row's query columns.
pub proof fn lemma_li_at(fp: Seq<PartView>, rel: Seq<Row>, map: Seq<int>, j: int)
    requires
        fp.len() == FACTS_PARTS,
        n_li(fp) == rel.len(),
        map.len() == rel.len(),
        0 <= j < rel.len(),
        0 <= map[j] < rel.len(),
        ({
            let tp = li_tp(fp);
            let srows = stored_rows(proj_all(rel, fd::stored_cols_t0()), map);
            &&& int_col_at(tp, LI_GROUPS as int, LI_PARTKEY_CODES as int, LI_PARTKEY_BASE as int, srows, 1)
            &&& num_col_at(tp, LI_GROUPS as int, LI_EXTENDEDPRICE_CODES as int, LI_EXTENDEDPRICE_BASE as int, srows, 5, 2)
            &&& num_col_at(tp, LI_GROUPS as int, LI_DISCOUNT_CODES as int, LI_DISCOUNT_BASE as int, srows, 6, 2)
            &&& date_col_at(tp, LI_GROUPS as int, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, srows, 10)
        }),
    ensures
        li_rows(fp)[j] == proj_all(rel, ca())[map[j]],
{
    hide(int_col_at);
    hide(num_col_at);
    hide(date_col_at);
    let i = map[j];
    let rel15 = proj_all(rel, fd::stored_cols_t0());
    let srows = stored_rows(rel15, map);
    assert(fd::stored_cols_t0().len() == 15);
    lemma_proj_all_index(rel, fd::stored_cols_t0());
    lemma_proj_all_index(rel, ca());
    assert(srows[j] == rel15[i]);
    assert(rel15[i] == proj(rel[i], fd::stored_cols_t0()));
    reveal(int_col_at);
    reveal(num_col_at);
    reveal(date_col_at);
    lemma_stored_row_cols(fp, srows, j);
    assert(srows[j][1] == rel[i][1]);
    assert(srows[j][5] == rel[i][5]);
    assert(srows[j][6] == rel[i][6]);
    assert(srows[j][10] == rel[i][10]);
    assert(li_rows(fp)[j] =~= proj_all(rel, ca())[i]);
}

/// For a bound database: the lineitem parts have the shape of `li_shape`, and the stored rows' query columns are a
/// permutation (the stored row map) of the lineitem rows' query columns.
pub proof fn lemma_li_link(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures ({
        let fp = sv.facts;
        let n = db.tables[0].len() as int;
        let map = lineitem_map(li_tp(fp), n);
        &&& li_shape(fp)
        &&& n_li(fp) == n
        &&& is_perm(map, n)
        &&& li_rows(fp) == stored_rows(proj_all(db.tables[0], ca()), map)
        &&& li_rows(fp).to_multiset() == proj_all(db.tables[0], ca()).to_multiset()
    }),
{
    hide(represents);
    hide(lineitem_ok);
    hide(orders_ok);
    hide(lineitem_cols_ok);
    hide(db_wf);
    hide(proj);
    hide(li_rows);
    hide(int_col_at);
    hide(num_col_at);
    hide(date_col_at);
    hide(table_layout_ok);
    hide(zone_at);
    let fp = sv.facts;
    let rels = fd::stored_relations(db);
    let rel = db.tables[0];
    let tp = li_tp(fp);
    assert(stored_ok(sv, db));
    assert(represents(fp, rels));
    lemma_li_facts(fp, rels);
    lemma_li_shape_parts(fp, rels);
    lemma_proj_all_index(rel, fd::stored_cols_t0());
    let n = rel.len() as int;
    let map = lineitem_map(tp, n);
    assert(lineitem_rows(tp, rels[0]) == stored_rows(proj_all(rel, fd::stored_cols_t0()), map));
    let xs = li_rows(fp);
    let xd = proj_all(rel, ca());
    assert forall|j: int| 0 <= j < n implies #[trigger] xs[j] == xd[map[j]] by {
        lemma_li_at(fp, rel, map, j);
    }
    lemma_proj_all_index(rel, ca());
    assert(xs.len() == n) by {
        reveal(li_rows);
    }
    assert(xs =~= stored_rows(xd, map));
    lemma_stored_rows_multiset(xd, map);
    // value bounds of price and discount (numeric(15, 2))
    reveal(db_wf);
    lemma_rows_typed(db);
    assert forall|j: int| 0 <= j < n implies abs_lt(#[trigger] price_at(fp, j), p15()) && abs_lt(disc_at(fp, j), p15()) by {
        let i = map[j];
        assert(xs[j] == xd[i]);
        assert(lrow_typed(rel[i]));
        reveal(proj);
        reveal(li_rows);
        assert(xs[j][1] == rel[i][5]);
        assert(xs[j][2] == rel[i][6]);
    }
    assert forall|j: int| 0 <= j < n implies abs_lt(#[trigger] disc_at(fp, j), p15()) by {
        assert(abs_lt(price_at(fp, j), p15()));
    }
}

} // verus!
