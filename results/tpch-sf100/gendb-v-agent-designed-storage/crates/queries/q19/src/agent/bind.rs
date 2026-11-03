//! What a database bound to the stored parts (`gendb_entry::bound_db`) gives the kernel and the proof.
//!
//! - lineitem (storage `facts`, clustered): the stored rows' query columns `model::li_rows` are the database's
//!   lineitem rows projected on `lcols()` = `[l_partkey, l_quantity, l_extendedprice, l_discount, l_shipinstruct,
//!   l_shipmode]` under the stored row map, a permutation (`lemma_li_link`); the parts have the shape the kernel reads
//!   (`model::li_shape`).
//! - part (storage `custpart`, canonical order): `model::pa_rows` are the part rows projected on `pcols()` =
//!   `[p_partkey, p_brand, p_size, p_container]` in order (`lemma_pa_link`), with the shape of `model::pa_shape`.
//! - the lineitem and part rows of a database of the schema are typed (`lrow_typed`, `prow_typed`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::numeric::*;
use crate::link::expr::{ival, tval};
use crate::link::query::{proj, proj_all};
use crate::link::source::lemma_proj_all_index;
use crate::schema::schema_spec;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::part_len;
use crate::gendb_entry::stores::{StoresView, stored_ok};
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::facts::declaration as fd;
use crate::stores::custpart::interface as cpi;
use crate::stores::custpart::interface::common::colfmt as cpc;
use crate::stores::custpart::declaration as cpd;
use crate::stores::li_partdir::interface as lpd;
use crate::stores::li_partdir::declaration as lpdd;
use super::model::*;

verus! {

// ------------------------------------------------------------------------------------------------ typing

/// A numeric(15, 2) value.
pub open spec fn num2(v: Val) -> bool {
    v == Val::Num { coeff: ival(v), scale: 2 } && abs_lt(ival(v), p15())
}

/// A bigint value.
pub open spec fn int8v(v: Val) -> bool {
    v == Val::Int(ival(v)) && i64::MIN <= ival(v) <= i64::MAX
}

/// A text value.
pub open spec fn textv(v: Val) -> bool {
    v == Val::Text(tval(v))
}

/// The lineitem columns the statement reads, typed.
pub open spec fn lrow_typed(r: Row) -> bool {
    &&& r.len() == 16
    &&& int8v(r[1])
    &&& num2(r[4]) && num2(r[5]) && num2(r[6])
    &&& textv(r[13]) && textv(r[14])
}

/// The part columns the statement reads, typed.
pub open spec fn prow_typed(r: Row) -> bool {
    &&& r.len() == 9
    &&& int8v(r[0])
    &&& textv(r[3])
    &&& int8v(r[5])
    &&& textv(r[6])
}

/// The typed rows of a database.
pub open spec fn rows_typed(db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& forall|i: int| 0 <= i < db.tables[0].len() ==> lrow_typed(#[trigger] db.tables[0][i])
    &&& forall|i: int| 0 <= i < db.tables[3].len() ==> prow_typed(#[trigger] db.tables[3][i])
}

pub proof fn lemma_pow10_15()
    ensures pow10(15) == p15(),
{
    assert(pow10(15) == p15()) by (compute);
}

/// The lineitem and part rows of a database of the schema are typed.
pub proof fn lemma_rows_typed(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures rows_typed(db),
{
    fd::lemma_declared_schema();
    cpd::lemma_declared_schema();
    lemma_pow10_15();
    let int8 = Column { ty: SqlType::Int8, nullable: false };
    let num = Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false };
    let text = Column { ty: SqlType::Text, nullable: false };
    assert(schema_spec()[0].columns.len() == 16) by (compute);
    assert(schema_spec()[0].columns[1] == int8) by (compute);
    assert(schema_spec()[0].columns[4] == num) by (compute);
    assert(schema_spec()[0].columns[5] == num) by (compute);
    assert(schema_spec()[0].columns[6] == num) by (compute);
    assert(schema_spec()[0].columns[13] == text) by (compute);
    assert(schema_spec()[0].columns[14] == text) by (compute);
    assert(schema_spec()[3].columns.len() == 9) by (compute);
    assert(schema_spec()[3].columns[0] == int8) by (compute);
    assert(schema_spec()[3].columns[3] == text) by (compute);
    assert(schema_spec()[3].columns[5] == int8) by (compute);
    assert(schema_spec()[3].columns[6] == text) by (compute);
    assert forall|i: int| 0 <= i < db.tables[0].len() implies lrow_typed(#[trigger] db.tables[0][i]) by {
        let r = db.tables[0][i];
        assert(row_in_table(r, db.schema[0]));
        assert(value_in_column(r[1], int8));
        assert(crate::spec::int::int_in_range(crate::spec::int::IntKind::Int8, ival(r[1])));
        assert(value_in_column(r[4], num));
        assert(value_in_column(r[5], num));
        assert(value_in_column(r[6], num));
        assert(value_in_column(r[13], text));
        assert(value_in_column(r[14], text));
    }
    assert forall|i: int| 0 <= i < db.tables[3].len() implies prow_typed(#[trigger] db.tables[3][i]) by {
        let r = db.tables[3][i];
        assert(row_in_table(r, db.schema[3]));
        assert(value_in_column(r[0], int8));
        assert(crate::spec::int::int_in_range(crate::spec::int::IntKind::Int8, ival(r[0])));
        assert(value_in_column(r[3], text));
        assert(value_in_column(r[5], int8));
        assert(crate::spec::int::int_in_range(crate::spec::int::IntKind::Int8, ival(r[5])));
        assert(value_in_column(r[6], text));
    }
}

// ------------------------------------------------------------------------------------------------ part

/// The part columns of the statement: p_partkey, p_brand, p_size, p_container.
pub open spec fn pcols() -> Seq<nat> {
    seq![0nat, 3nat, 5nat, 6nat]
}

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

/// One row of an integer column.
pub proof fn lemma_cp_int_row(tp: Seq<PartView>, gp: int, cp: int, bp: int, rows: Seq<Row>, c: int, j: int)
    requires cpc::int_col_at(tp, gp, cp, bp, rows, c), 0 <= j < rows.len(),
    ensures rows[j][c] == Val::Int(cpc::for_at(cpc::gs_at(tp, gp), tp[bp], tp[cp], j)),
{
}

/// One row of a dictionary column: its entry index is inside the dictionary.
pub proof fn lemma_cp_dict_row(tp: Seq<PartView>, gp: int, cp: int, bp: int, op: int, yp: int, rows: Seq<Row>, c: int, j: int)
    requires cpc::dict_col_at(tp, gp, cp, bp, op, yp, rows, c), 0 <= j < rows.len(),
    ensures
        0 <= cpc::for_at(cpc::gs_at(tp, gp), tp[bp], tp[cp], j) < cpc::u64s(tp[op]).len() - 1,
        rows[j][c] == Val::Text(cpc::text_of(cpc::u64s(tp[op]), cpc::u8s(tp[yp]), cpc::for_at(cpc::gs_at(tp, gp), tp[bp], tp[cp], j))),
{
    let _ = rows[j][c];
}

/// The part facts of `part_ok`: shapes, and every stored part row's values.
pub proof fn lemma_pa_cols(cp: Seq<PartView>, rel: Seq<Row>)
    requires
        cp.len() == cpi::CUSTPART_PARTS,
        cpi::part_ok(pa_tp(cp), rel),
        forall|j: int| 0 <= j < rel.len() ==> prow_typed(#[trigger] rel[j]),
    ensures
        pa_shape(cp),
        n_pa(cp) == rel.len(),
        forall|j: int| 0 <= j < n_pa(cp) ==> #[trigger] pa_rows(cp)[j] == proj(rel[j], pcols()),
{
    hide(cpc::text_col_at);
    hide(cpc::int_col_at);
    hide(cpc::dict_col_at);
    hide(cpc::num_col_at);
    let tp = pa_tp(cp);
    assert forall|k: int| 0 <= k < cpi::PA_PARTS implies #[trigger] tp[k] == cp[pp(k as usize)] by {}
    assert(tp[cpi::PA_GROUPS as int] == cp[pp(cpi::PA_GROUPS)]);
    assert(tp[cpi::PA_LAYOUT as int] == cp[pp(cpi::PA_LAYOUT)]);
    let n = rel.len() as int;
    let bs = cpc::u64s(tp[cpi::PA_LAYOUT as int])[1] as int;
    cpc::lemma_uniform_groups(tp[cpi::PA_GROUPS as int], n, bs);
    assert(cpc::gs_at(tp, cpi::PA_GROUPS as int) == pa_gs(cp));
    lemma_pa_shape_parts(cp, rel);
    assert(n_pa(cp) == n);
    assert forall|j: int| 0 <= j < n implies #[trigger] pa_rows(cp)[j] == proj(rel[j], pcols()) by {
        lemma_pa_row_vals(cp, rel, j);
    }
    assert forall|j: int| 0 <= j < n implies 0 <= #[trigger] bidx_at(cp, j) < n_bd(cp) by {
        lemma_pa_row_vals(cp, rel, j);
    }
    assert forall|j: int| 0 <= j < n implies 0 <= #[trigger] cidx_at(cp, j) < n_cd(cp) by {
        lemma_pa_row_vals(cp, rel, j);
    }
    assert forall|j: int| 0 <= j < n implies i64::MIN <= #[trigger] pkey_at(cp, j) <= i64::MAX by {
        lemma_pa_row_vals(cp, rel, j);
    }
    assert forall|j: int| 0 <= j < n implies i64::MIN <= #[trigger] size_at(cp, j) <= i64::MAX by {
        lemma_pa_row_vals(cp, rel, j);
    }
}

/// The part shapes of `part_ok`.
proof fn lemma_pa_shape_parts(cp: Seq<PartView>, rel: Seq<Row>)
    requires
        cp.len() == cpi::CUSTPART_PARTS,
        cpi::part_ok(pa_tp(cp), rel),
    ensures ({
        let n = n_pa(cp);
        let ng = pa_gs(cp).len() - 1;
        &&& n == rel.len()
        &&& cp[pp(cpi::PA_LAYOUT)] is U64 && cpc::u64s(cp[pp(cpi::PA_LAYOUT)]).len() == 2
        &&& cpc::groups_part_ok(cp[pp(cpi::PA_GROUPS)], n, pa_bs(cp))
        &&& cp[pp(cpi::PA_PARTKEY_CODES)] is U32
        &&& cp[pp(cpi::PA_PARTKEY_BASE)] is I64 && part_len(cp[pp(cpi::PA_PARTKEY_BASE)]) == ng
        &&& cp[pp(cpi::PA_BRAND_CODES)] is U8 && part_len(cp[pp(cpi::PA_BRAND_CODES)]) == n
        &&& cp[pp(cpi::PA_BRAND_BASE)] is U64 && part_len(cp[pp(cpi::PA_BRAND_BASE)]) == ng
        &&& cp[pp(cpi::PA_SIZE_CODES)] is U8 && part_len(cp[pp(cpi::PA_SIZE_CODES)]) == n
        &&& cp[pp(cpi::PA_SIZE_BASE)] is I64 && part_len(cp[pp(cpi::PA_SIZE_BASE)]) == ng
        &&& cp[pp(cpi::PA_CONTAINER_CODES)] is U8 && part_len(cp[pp(cpi::PA_CONTAINER_CODES)]) == n
        &&& cp[pp(cpi::PA_CONTAINER_BASE)] is U64 && part_len(cp[pp(cpi::PA_CONTAINER_BASE)]) == ng
        &&& cp[pp(cpi::PA_BRAND_DICT_OFFS)] is U64 && cp[pp(cpi::PA_BRAND_DICT_BYTES)] is U8
        &&& bd_o(cp).len() >= 1 && cpc::text_parts_wf(bd_o(cp), bd_y(cp), n_bd(cp))
        &&& cp[pp(cpi::PA_CONTAINER_DICT_OFFS)] is U64 && cp[pp(cpi::PA_CONTAINER_DICT_BYTES)] is U8
        &&& cd_o(cp).len() >= 1 && cpc::text_parts_wf(cd_o(cp), cd_y(cp), n_cd(cp))
        &&& cpc::dict_sorted(bd_o(cp), bd_y(cp), n_bd(cp))
        &&& cpc::dict_sorted(cd_o(cp), cd_y(cp), n_cd(cp))
    }),
{
    hide(cpc::text_col_at);
    hide(cpc::num_col_at);
    let tp = pa_tp(cp);
    assert forall|k: int| 0 <= k < cpi::PA_PARTS implies #[trigger] tp[k] == cp[pp(k as usize)] by {}
    let n = rel.len() as int;
    let bs = cpc::u64s(tp[cpi::PA_LAYOUT as int])[1] as int;
    cpc::lemma_uniform_groups(tp[cpi::PA_GROUPS as int], n, bs);
    assert(tp[cpi::PA_PARTKEY_CODES as int] == cp[pp(cpi::PA_PARTKEY_CODES)]);
    assert(tp[cpi::PA_PARTKEY_BASE as int] == cp[pp(cpi::PA_PARTKEY_BASE)]);
    assert(tp[cpi::PA_BRAND_CODES as int] == cp[pp(cpi::PA_BRAND_CODES)]);
    assert(tp[cpi::PA_BRAND_BASE as int] == cp[pp(cpi::PA_BRAND_BASE)]);
    assert(tp[cpi::PA_BRAND_DICT_OFFS as int] == cp[pp(cpi::PA_BRAND_DICT_OFFS)]);
    assert(tp[cpi::PA_BRAND_DICT_BYTES as int] == cp[pp(cpi::PA_BRAND_DICT_BYTES)]);
    assert(tp[cpi::PA_SIZE_CODES as int] == cp[pp(cpi::PA_SIZE_CODES)]);
    assert(tp[cpi::PA_SIZE_BASE as int] == cp[pp(cpi::PA_SIZE_BASE)]);
    assert(tp[cpi::PA_CONTAINER_CODES as int] == cp[pp(cpi::PA_CONTAINER_CODES)]);
    assert(tp[cpi::PA_CONTAINER_BASE as int] == cp[pp(cpi::PA_CONTAINER_BASE)]);
    assert(tp[cpi::PA_CONTAINER_DICT_OFFS as int] == cp[pp(cpi::PA_CONTAINER_DICT_OFFS)]);
    assert(tp[cpi::PA_CONTAINER_DICT_BYTES as int] == cp[pp(cpi::PA_CONTAINER_DICT_BYTES)]);
    assert(tp[cpi::PA_GROUPS as int] == cp[pp(cpi::PA_GROUPS)]);
    assert(tp[cpi::PA_LAYOUT as int] == cp[pp(cpi::PA_LAYOUT)]);
}

/// Stored part row `j`'s values are its database row's values, with dictionary indices inside the dictionaries
/// and integers inside int8.
proof fn lemma_pa_row_vals(cp: Seq<PartView>, rel: Seq<Row>, j: int)
    requires
        cp.len() == cpi::CUSTPART_PARTS,
        cpi::part_ok(pa_tp(cp), rel),
        forall|i: int| 0 <= i < rel.len() ==> prow_typed(#[trigger] rel[i]),
        0 <= j < rel.len(),
    ensures
        pa_rows(cp)[j] == proj(rel[j], pcols()),
        0 <= bidx_at(cp, j) < n_bd(cp),
        0 <= cidx_at(cp, j) < n_cd(cp),
        i64::MIN <= pkey_at(cp, j) <= i64::MAX,
        i64::MIN <= size_at(cp, j) <= i64::MAX,
{
    hide(cpc::text_col_at);
    hide(cpc::num_col_at);
    hide(cpc::int_col_at);
    hide(cpc::dict_col_at);
    let tp = pa_tp(cp);
    assert forall|k: int| 0 <= k < cpi::PA_PARTS implies #[trigger] tp[k] == cp[pp(k as usize)] by {}
    assert(tp[cpi::PA_PARTKEY_CODES as int] == cp[pp(cpi::PA_PARTKEY_CODES)]);
    assert(tp[cpi::PA_PARTKEY_BASE as int] == cp[pp(cpi::PA_PARTKEY_BASE)]);
    assert(tp[cpi::PA_BRAND_CODES as int] == cp[pp(cpi::PA_BRAND_CODES)]);
    assert(tp[cpi::PA_BRAND_BASE as int] == cp[pp(cpi::PA_BRAND_BASE)]);
    assert(tp[cpi::PA_BRAND_DICT_OFFS as int] == cp[pp(cpi::PA_BRAND_DICT_OFFS)]);
    assert(tp[cpi::PA_BRAND_DICT_BYTES as int] == cp[pp(cpi::PA_BRAND_DICT_BYTES)]);
    assert(tp[cpi::PA_SIZE_CODES as int] == cp[pp(cpi::PA_SIZE_CODES)]);
    assert(tp[cpi::PA_SIZE_BASE as int] == cp[pp(cpi::PA_SIZE_BASE)]);
    assert(tp[cpi::PA_CONTAINER_CODES as int] == cp[pp(cpi::PA_CONTAINER_CODES)]);
    assert(tp[cpi::PA_CONTAINER_BASE as int] == cp[pp(cpi::PA_CONTAINER_BASE)]);
    assert(tp[cpi::PA_CONTAINER_DICT_OFFS as int] == cp[pp(cpi::PA_CONTAINER_DICT_OFFS)]);
    assert(tp[cpi::PA_CONTAINER_DICT_BYTES as int] == cp[pp(cpi::PA_CONTAINER_DICT_BYTES)]);
    assert(tp[cpi::PA_GROUPS as int] == cp[pp(cpi::PA_GROUPS)]);
    let g = cpi::PA_GROUPS as int;
    lemma_cp_int_row(tp, g, cpi::PA_PARTKEY_CODES as int, cpi::PA_PARTKEY_BASE as int, rel, 0, j);
    lemma_cp_dict_row(tp, g, cpi::PA_BRAND_CODES as int, cpi::PA_BRAND_BASE as int, cpi::PA_BRAND_DICT_OFFS as int,
        cpi::PA_BRAND_DICT_BYTES as int, rel, 3, j);
    lemma_cp_int_row(tp, g, cpi::PA_SIZE_CODES as int, cpi::PA_SIZE_BASE as int, rel, 5, j);
    lemma_cp_dict_row(tp, g, cpi::PA_CONTAINER_CODES as int, cpi::PA_CONTAINER_BASE as int, cpi::PA_CONTAINER_DICT_OFFS as int,
        cpi::PA_CONTAINER_DICT_BYTES as int, rel, 6, j);
    let r = rel[j];
    assert(prow_typed(r));
    assert(r[0] == Val::Int(pkey_at(cp, j)));
    assert(r[3] == Val::Text(bdict(cp, bidx_at(cp, j))));
    assert(r[5] == Val::Int(size_at(cp, j)));
    assert(r[6] == Val::Text(cdict(cp, cidx_at(cp, j))));
    assert(proj(r, pcols()) =~= pa_row(cp, j));
}

/// For a bound database: the part parts have the shape of `pa_shape`, and the stored part rows are the part rows
/// projected on `pcols()`.
pub proof fn lemma_pa_link(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        pa_shape(sv.custpart),
        n_pa(sv.custpart) == db.tables[3].len(),
        pa_rows(sv.custpart) == proj_all(db.tables[3], pcols()),
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
    assert forall|i: int| 0 <= i < rel.len() implies (#[trigger] rel[i]).len() == 9 by {
        assert(prow_typed(rel[i]));
    }
    lemma_proj_full(rel, cpd::stored_cols_t1(), 9);
    assert(rels[1] == rel);
    assert(cpi::part_ok(pa_tp(cp), rel));
    assert forall|j: int| 0 <= j < rel.len() implies prow_typed(#[trigger] rel[j]) by {}
    lemma_pa_cols(cp, rel);
    lemma_proj_all_index(rel, pcols());
    assert(pa_rows(cp) =~= proj_all(rel, pcols()));
}

// ------------------------------------------------------------------------------------------------ lineitem

/// The lineitem columns of the statement: l_partkey, l_quantity, l_extendedprice, l_discount, l_shipinstruct,
/// l_shipmode.
pub open spec fn lcols() -> Seq<nat> {
    seq![1nat, 4nat, 5nat, 6nat, 13nat, 14nat]
}

/// The parts of table lineitem in storage facts.
pub open spec fn li_tp(fp: Seq<PartView>) -> Seq<PartView> {
    fp.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int)
}

/// The column facts of `lineitem_cols_ok` the kernel reads, over the stored rows `srows`.
pub open spec fn li_col_facts(fp: Seq<PartView>, srows: Seq<Row>) -> bool {
    let tp = li_tp(fp);
    &&& int_col_at(tp, LI_GROUPS as int, LI_PARTKEY_CODES as int, LI_PARTKEY_BASE as int, srows, 1)
    &&& num_col_at(tp, LI_GROUPS as int, LI_QUANTITY_CODES as int, LI_QUANTITY_BASE as int, srows, 4, 2)
    &&& num_col_at(tp, LI_GROUPS as int, LI_EXTENDEDPRICE_CODES as int, LI_EXTENDEDPRICE_BASE as int, srows, 5, 2)
    &&& num_col_at(tp, LI_GROUPS as int, LI_DISCOUNT_CODES as int, LI_DISCOUNT_BASE as int, srows, 6, 2)
    &&& dict_col_at(tp, LI_GROUPS as int, LI_SHIPINSTRUCT_CODES as int, LI_SHIPINSTRUCT_BASE as int,
            LI_SHIPINSTRUCT_DICT_OFFS as int, LI_SHIPINSTRUCT_DICT_BYTES as int, srows, 13)
    &&& dict_col_at(tp, LI_GROUPS as int, LI_SHIPMODE_CODES as int, LI_SHIPMODE_BASE as int,
            LI_SHIPMODE_DICT_OFFS as int, LI_SHIPMODE_DICT_BYTES as int, srows, 14)
}

/// One row of a dictionary column of facts: its entry index is inside the dictionary.
pub proof fn lemma_fp_dict_row(tp: Seq<PartView>, gp: int, cp: int, bp: int, op: int, yp: int, rows: Seq<Row>, c: int, j: int)
    requires dict_col_at(tp, gp, cp, bp, op, yp, rows, c), 0 <= j < rows.len(),
    ensures
        0 <= for_at(gs_at(tp, gp), tp[bp], tp[cp], j) < u64s(tp[op]).len() - 1,
{
    let _ = rows[j][c];
}

/// The facts of `represents` about the lineitem parts.
pub proof fn lemma_li_facts(fp: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires represents(fp, rels),
    ensures ({
        let tp = li_tp(fp);
        let n = rels[0].len() as int;
        let srows = lineitem_rows(tp, rels[0]);
        &&& fp.len() == FACTS_PARTS
        &&& table_layout_ok(tp, n)
        &&& is_perm(lineitem_map(tp, n), n)
        &&& li_col_facts(fp, srows)
        &&& srows.len() == n
        &&& tp[LI_PARTKEY_CODES as int] is U32 && tp[LI_QUANTITY_CODES as int] is U16
        &&& tp[LI_EXTENDEDPRICE_CODES as int] is U32 && tp[LI_DISCOUNT_CODES as int] is U8
        &&& tp[LI_SHIPINSTRUCT_CODES as int] is U8 && tp[LI_SHIPMODE_CODES as int] is U8
        &&& tp[LI_KEYIDX_CODES as int] is U32 && tp[LI_KEYIDX_BASE as int] is U64
        &&& tp[LI_KEYIDX_KIND as int] is U64 && u64s(tp[LI_KEYIDX_KIND as int]).len() == 1
        &&& crate::stores::facts::interface::common::keyidx::keyidx_ok(u32s(tp[LI_PARTKEY_CODES as int]),
                i64s(tp[LI_PARTKEY_BASE as int]), u32s(tp[LI_KEYIDX_CODES as int]), u64s(tp[LI_KEYIDX_BASE as int]),
                u64s(tp[LI_LAYOUT as int])[1] as int, u64s(tp[LI_KEYIDX_KIND as int])[0], n)
    }),
{
}

/// One stored lineitem row's query columns are its database row's query columns.
pub proof fn lemma_li_at(fp: Seq<PartView>, rel: Seq<Row>, map: Seq<int>, j: int)
    requires
        fp.len() == FACTS_PARTS,
        n_li(fp) == rel.len(),
        map.len() == rel.len(),
        0 <= j < rel.len(),
        0 <= map[j] < rel.len(),
        li_col_facts(fp, stored_rows(proj_all(rel, fd::stored_cols_t0()), map)),
    ensures
        li_rows(fp)[j] == proj_all(rel, lcols())[map[j]],
{
    hide(int_col_at);
    hide(num_col_at);
    hide(dict_col_at);
    let i = map[j];
    let rel15 = proj_all(rel, fd::stored_cols_t0());
    let srows = stored_rows(rel15, map);
    let tp = li_tp(fp);
    assert(fd::stored_cols_t0().len() == 15);
    lemma_proj_all_index(rel, fd::stored_cols_t0());
    lemma_proj_all_index(rel, lcols());
    assert(srows[j] == rel15[i]);
    assert(rel15[i] == proj(rel[i], fd::stored_cols_t0()));
    assert forall|k: int| 0 <= k < 48 implies #[trigger] tp[k] == fp[k] by {}
    reveal(int_col_at);
    reveal(num_col_at);
    reveal(dict_col_at);
    assert(srows[j][1] == Val::Int(lpk_at(fp, j)));
    assert(srows[j][4] == (Val::Num { coeff: qty_at(fp, j), scale: 2 }));
    assert(srows[j][5] == (Val::Num { coeff: price_at(fp, j), scale: 2 }));
    assert(srows[j][6] == (Val::Num { coeff: disc_at(fp, j), scale: 2 }));
    assert(srows[j][13] == Val::Text(sdict(fp, sidx_at(fp, j))));
    assert(srows[j][14] == Val::Text(mdict(fp, midx_at(fp, j))));
    assert(srows[j][1] == rel[i][1]);
    assert(srows[j][4] == rel[i][4]);
    assert(srows[j][5] == rel[i][5]);
    assert(srows[j][6] == rel[i][6]);
    assert(srows[j][13] == rel[i][13]);
    assert(srows[j][14] == rel[i][14]);
    assert(li_rows(fp)[j] =~= proj_all(rel, lcols())[i]);
}

/// The shape facts of the lineitem parts (without the value facts).
pub proof fn lemma_li_shape_parts(fp: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires represents(fp, rels),
    ensures
        n_li(fp) == rels[0].len(),
        fp.len() == FACTS_PARTS,
        fp[LI_LAYOUT as int] is U64 && u64s(fp[LI_LAYOUT as int]).len() == 2,
        groups_part_ok(fp[LI_GROUPS as int], n_li(fp), li_bs(fp)),
        fp[LI_PARTKEY_CODES as int] is U32 && part_len(fp[LI_PARTKEY_CODES as int]) == n_li(fp),
        fp[LI_QUANTITY_CODES as int] is U16,
        fp[LI_EXTENDEDPRICE_CODES as int] is U32 && part_len(fp[LI_EXTENDEDPRICE_CODES as int]) == n_li(fp),
        fp[LI_DISCOUNT_CODES as int] is U8 && part_len(fp[LI_DISCOUNT_CODES as int]) == n_li(fp),
        fp[LI_SHIPINSTRUCT_CODES as int] is U8 && part_len(fp[LI_SHIPINSTRUCT_CODES as int]) == n_li(fp),
        fp[LI_SHIPMODE_CODES as int] is U8 && part_len(fp[LI_SHIPMODE_CODES as int]) == n_li(fp),
        li_ibase(fp, LI_PARTKEY_BASE as int),
        li_ibase(fp, LI_QUANTITY_BASE as int),
        li_ibase(fp, LI_EXTENDEDPRICE_BASE as int),
        li_ibase(fp, LI_DISCOUNT_BASE as int),
        li_ubase(fp, LI_SHIPINSTRUCT_BASE as int),
        li_ubase(fp, LI_SHIPMODE_BASE as int),
        fp[LI_SHIPINSTRUCT_DICT_OFFS as int] is U64 && fp[LI_SHIPINSTRUCT_DICT_BYTES as int] is U8,
        sd_o(fp).len() >= 1 && text_parts_wf(sd_o(fp), sd_y(fp), n_sd(fp)),
        fp[LI_SHIPMODE_DICT_OFFS as int] is U64 && fp[LI_SHIPMODE_DICT_BYTES as int] is U8,
        md_o(fp).len() >= 1 && text_parts_wf(md_o(fp), md_y(fp), n_md(fp)),
        dict_sorted(sd_o(fp), sd_y(fp), n_sd(fp)),
        dict_sorted(md_o(fp), md_y(fp), n_md(fp)),
        fp[LI_KEYIDX_CODES as int] is U32 && fp[LI_KEYIDX_BASE as int] is U64,
        fp[LI_KEYIDX_KIND as int] is U64 && u64s(fp[LI_KEYIDX_KIND as int]).len() == 1,
        kx_ok(fp),
{
    hide(represents);
    lemma_li_facts(fp, rels);
    let tp = li_tp(fp);
    let n = rels[0].len() as int;
    let srows = lineitem_rows(tp, rels[0]);
    assert forall|k: int| 0 <= k < 48 implies #[trigger] tp[k] == fp[k] by {}
    let bs = u64s(tp[LI_LAYOUT as int])[1] as int;
    lemma_uniform_groups(tp[LI_GROUPS as int], n, bs);
    assert(li_gs(fp) == gs_at(tp, LI_GROUPS as int));
    assert(tp[LI_QUANTITY_CODES as int] == fp[LI_QUANTITY_CODES as int]);
    assert(n_li(fp) == n);
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
        &&& li_rows(fp) == stored_rows(proj_all(db.tables[0], lcols()), map)
        &&& li_rows(fp).to_multiset() == proj_all(db.tables[0], lcols()).to_multiset()
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
    hide(dict_col_at);
    hide(table_layout_ok);
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
    let xd = proj_all(rel, lcols());
    assert forall|j: int| 0 <= j < n implies #[trigger] xs[j] == xd[map[j]] by {
        lemma_li_at(fp, rel, map, j);
    }
    lemma_proj_all_index(rel, lcols());
    assert(xs.len() == n) by {
        reveal(li_rows);
    }
    assert(xs =~= stored_rows(xd, map));
    lemma_stored_rows_multiset(xd, map);
    // value facts from the typed rows
    reveal(db_wf);
    lemma_rows_typed(db);
    reveal(dict_col_at);
    let srows = lineitem_rows(tp, rels[0]);
    assert forall|j: int| 0 <= j < n implies {
        &&& 0 <= #[trigger] sidx_at(fp, j) < n_sd(fp)
        &&& 0 <= midx_at(fp, j) < n_md(fp)
        &&& i64::MIN <= lpk_at(fp, j) <= i64::MAX
        &&& abs_lt(qty_at(fp, j), p15())
        &&& abs_lt(price_at(fp, j), p15())
        &&& abs_lt(disc_at(fp, j), p15())
    } by {
        let i = map[j];
        assert(xs[j] == xd[i]);
        assert(lrow_typed(rel[i]));
        reveal(proj);
        reveal(li_rows);
        assert(xs[j][0] == rel[i][1]);
        assert(xs[j][1] == rel[i][4]);
        assert(xs[j][2] == rel[i][5]);
        assert(xs[j][3] == rel[i][6]);
        assert(tp[LI_SHIPINSTRUCT_CODES as int] == fp[LI_SHIPINSTRUCT_CODES as int]);
        assert(tp[LI_SHIPINSTRUCT_BASE as int] == fp[LI_SHIPINSTRUCT_BASE as int]);
        assert(tp[LI_SHIPINSTRUCT_DICT_OFFS as int] == fp[LI_SHIPINSTRUCT_DICT_OFFS as int]);
        assert(tp[LI_SHIPMODE_CODES as int] == fp[LI_SHIPMODE_CODES as int]);
        assert(tp[LI_SHIPMODE_BASE as int] == fp[LI_SHIPMODE_BASE as int]);
        assert(tp[LI_SHIPMODE_DICT_OFFS as int] == fp[LI_SHIPMODE_DICT_OFFS as int]);
        assert(tp[LI_GROUPS as int] == fp[LI_GROUPS as int]);
        assert(tp[LI_SHIPINSTRUCT_DICT_BYTES as int] == fp[LI_SHIPINSTRUCT_DICT_BYTES as int]);
        assert(tp[LI_SHIPMODE_DICT_BYTES as int] == fp[LI_SHIPMODE_DICT_BYTES as int]);
        lemma_fp_dict_row(tp, LI_GROUPS as int, LI_SHIPINSTRUCT_CODES as int, LI_SHIPINSTRUCT_BASE as int,
            LI_SHIPINSTRUCT_DICT_OFFS as int, LI_SHIPINSTRUCT_DICT_BYTES as int, srows, 13, j);
        lemma_fp_dict_row(tp, LI_GROUPS as int, LI_SHIPMODE_CODES as int, LI_SHIPMODE_BASE as int,
            LI_SHIPMODE_DICT_OFFS as int, LI_SHIPMODE_DICT_BYTES as int, srows, 14, j);
        assert(0 <= sidx_at(fp, j) < n_sd(fp));
        assert(0 <= midx_at(fp, j) < n_md(fp));
    }
    assert forall|s: int| 0 <= s < n implies 0 <= #[trigger] midx_at(fp, s) < n_md(fp) by {
        assert(0 <= sidx_at(fp, s) < n_sd(fp));
    }
    assert forall|s: int| 0 <= s < n implies i64::MIN <= #[trigger] lpk_at(fp, s) <= i64::MAX by {
        assert(0 <= sidx_at(fp, s) < n_sd(fp));
    }
    assert forall|s: int| 0 <= s < n implies abs_lt(#[trigger] qty_at(fp, s), p15()) by {
        assert(0 <= sidx_at(fp, s) < n_sd(fp));
    }
    assert forall|s: int| 0 <= s < n implies abs_lt(#[trigger] price_at(fp, s), p15()) by {
        assert(0 <= sidx_at(fp, s) < n_sd(fp));
    }
    assert forall|s: int| 0 <= s < n implies abs_lt(#[trigger] disc_at(fp, s), p15()) by {
        assert(0 <= sidx_at(fp, s) < n_sd(fp));
    }
}

// ------------------------------------------------------------------------------------------------ key directory

/// The part types of storage `li_partdir`'s directory (its values are only used as checked guesses).
pub open spec fn dir_shape(lp: Seq<PartView>) -> bool {
    &&& lp.len() == lpd::LI_PARTDIR_PARTS
    &&& lp[lpd::DIR_META as int] is I64 && lpd::i64s(lp[lpd::DIR_META as int]).len() == 2
    &&& lp[lpd::DIR_OFFS as int] is U32
}

/// For a bound database: the directory parts have their types.
pub proof fn lemma_dir_link(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures dir_shape(sv.li_partdir),
{
    assert(stored_ok(sv, db));
    assert(lpd::represents(sv.li_partdir, lpdd::stored_relations(db)));
}

} // verus!
