//! Column views of the three flat storages the query reads (`flat_lineitem`, `flat_orders`, `flat_customer`) and
//! how they denote the database tables.
//!
//! Every column the query touches is one stored part (a plain array in source row order); `lk(sv)[i]` is
//! `l_orderkey` of lineitem row `i`, `od(sv)[j]` is `o_orderdate` of orders row `j` (days since 1970-01-01), and so
//! on. For a database `db` bound to the parts (`bound_db`), row `i` of table `t` has these values at the columns'
//! table ordinals, and every value lies in its declared domain (`db_wf`); the `lemma_*_row` lemmas state exactly the
//! facts the query needs, one row at a time (no quantifier to instantiate).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::typing::*;
use crate::spec::types::*;
use crate::spec::datetime::*;
use crate::gendb_entry::stores::{StoresView, stored_ok};
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::link::query::{text_at, TextView, proj_all, proj};
use crate::link::source::{lemma_proj_all_index, rows_in_columns};
use crate::schema::schema_spec;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_lineitem::declaration as lid;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_orders::declaration as oid;
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_customer::declaration as cid;

verus! {

// ------------------------------------------------------------------------------------------------ column views

/// `l_orderkey` of every lineitem row.
pub open spec fn lk(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_ORDERKEY as int]) }

/// `l_shipdate` of every lineitem row (days since 1970-01-01).
pub open spec fn ls(sv: StoresView) -> Seq<i32> { li::i32s(sv.flat_lineitem[li::L_SHIPDATE as int]) }

/// `l_extendedprice` coefficients (scale 2).
pub open spec fn lp(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_EXTENDEDPRICE as int]) }

/// `l_discount` coefficients (scale 2).
pub open spec fn ld(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_DISCOUNT as int]) }

/// `o_orderkey` of every orders row.
pub open spec fn ok(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_ORDERKEY as int]) }

/// `o_custkey` of every orders row.
pub open spec fn oc(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_CUSTKEY as int]) }

/// `o_orderdate` of every orders row (days since 1970-01-01).
pub open spec fn od(sv: StoresView) -> Seq<i32> { oi::i32s(sv.flat_orders[oi::O_ORDERDATE as int]) }

/// `o_shippriority` of every orders row.
pub open spec fn os(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_SHIPPRIORITY as int]) }

/// `c_custkey` of every customer row.
pub open spec fn ck(sv: StoresView) -> Seq<i64> { ci::i64s(sv.flat_customer[ci::C_CUSTKEY as int]) }

/// The `c_mktsegment` text column (offsets and bytes parts).
pub open spec fn cseg_col(sv: StoresView) -> TextView {
    ci::text_view(sv.flat_customer, ci::C_MKTSEGMENT_OFFSETS as int, ci::C_MKTSEGMENT_BYTES as int)
}

/// `c_mktsegment` of customer row `r` (its bytes).
pub open spec fn cseg(sv: StoresView, r: int) -> Seq<u8> { text_at(cseg_col(sv), r) }

/// Row counts of the three tables.
pub open spec fn n_l(sv: StoresView) -> int { lk(sv).len() as int }
pub open spec fn n_o(sv: StoresView) -> int { ok(sv).len() as int }
pub open spec fn n_c(sv: StoresView) -> int { ck(sv).len() as int }

/// The parts have the shape of the three flat storages: every column the query reads has one value per row, and
/// the segment text column is well formed. (A consequence of `bound_db`, `lemma_parts_shape`.)
pub open spec fn parts_shape(sv: StoresView) -> bool {
    &&& li::parts_wf(sv.flat_lineitem, n_l(sv))
    &&& oi::parts_wf(sv.flat_orders, n_o(sv))
    &&& ci::parts_wf(sv.flat_customer, n_c(sv))
}

/// Values of the declared numeric(15,2) columns: `|coefficient| < 10^15`.
pub open spec fn num15(c: i128) -> bool { -1_000_000_000_000_000 < c < 1_000_000_000_000_000 }

// ------------------------------------------------------------------------------------------------ table facts

/// The parts of a bound database have the storages' shape, and the tables have the parts' row counts.
pub proof fn lemma_parts_shape(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        parts_shape(sv),
        db.tables.len() == 8,
        db.tables[0].len() == n_l(sv),
        db.tables[1].len() == n_o(sv),
        db.tables[2].len() == n_c(sv),
        ls(sv).len() == n_l(sv), lp(sv).len() == n_l(sv), ld(sv).len() == n_l(sv),
        oc(sv).len() == n_o(sv), od(sv).len() == n_o(sv), os(sv).len() == n_o(sv),
{
    lid::lemma_declared_schema();
    let lrels = lid::stored_relations(db);
    let orels = oid::stored_relations(db);
    let crels = cid::stored_relations(db);
    lemma_proj_all_index(db.tables[0], lid::stored_cols_t0());
    lemma_proj_all_index(db.tables[1], oid::stored_cols_t0());
    lemma_proj_all_index(db.tables[2], cid::stored_cols_t0());
    assert(lrels[0].len() == db.tables[0].len());
    assert(orels[0].len() == db.tables[1].len());
    assert(crels[0].len() == db.tables[2].len());
}

/// Lineitem row `i`: arity, `l_orderkey`, `l_extendedprice`, `l_discount`, `l_shipdate`, and the numeric bounds.
pub proof fn lemma_lineitem_row(sv: StoresView, db: Database, i: int)
    requires bound_db(sv, db), 0 <= i < db.tables[0].len(),
    ensures
        db.tables[0][i].len() == 16,
        db.tables[0][i][0] == Val::Int(lk(sv)[i] as int),
        db.tables[0][i][5] == (Val::Num { coeff: lp(sv)[i] as int, scale: 2 }),
        db.tables[0][i][6] == (Val::Num { coeff: ld(sv)[i] as int, scale: 2 }),
        db.tables[0][i][10] == date32_val(ls(sv)[i]),
        num15(lp(sv)[i]),
        num15(ld(sv)[i]),
{
    lemma_parts_shape(sv, db);
    lid::lemma_declared_schema();
    lid::lemma_stored_relations(db);
    let t = db.tables[0];
    let cols = lid::stored_cols_t0();
    let rels = lid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][i] == li::row_at(sv.flat_lineitem, i));
    assert(rels[0][i] == proj(t[i], cols));
    assert(row_in_table(t[i], db.schema[0]));
    let r = li::row_at(sv.flat_lineitem, i);
    assert(cols[0] == 0 && cols[5] == 5 && cols[6] == 6 && cols[10] == 10);
    assert(proj(t[i], cols)[0] == t[i][0]);
    assert(proj(t[i], cols)[5] == t[i][5]);
    assert(proj(t[i], cols)[6] == t[i][6]);
    assert(proj(t[i], cols)[10] == t[i][10]);
    let cs = lid::stored_columns_t0();
    assert(value_in_column(rels[0][i][5], cs[5]));
    assert(value_in_column(rels[0][i][6], cs[6]));
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
}

/// Orders row `j`: arity, `o_orderkey`, `o_custkey`, `o_orderdate`, `o_shippriority`.
pub proof fn lemma_orders_row(sv: StoresView, db: Database, j: int)
    requires bound_db(sv, db), 0 <= j < db.tables[1].len(),
    ensures
        db.tables[1][j].len() == 9,
        db.tables[1][j][0] == Val::Int(ok(sv)[j] as int),
        db.tables[1][j][1] == Val::Int(oc(sv)[j] as int),
        db.tables[1][j][4] == date32_val(od(sv)[j]),
        db.tables[1][j][7] == Val::Int(os(sv)[j] as int),
        od(sv)[j] as int - 10957 >= -2451545,
{
    lemma_parts_shape(sv, db);
    oid::lemma_declared_schema();
    let t = db.tables[1];
    let cols = oid::stored_cols_t0();
    let rels = oid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][j] == oi::row_at(sv.flat_orders, j));
    assert(rels[0][j] == proj(t[j], cols));
    assert(row_in_table(t[j], db.schema[1]));
    assert(cols[0] == 0 && cols[1] == 1 && cols[4] == 4 && cols[7] == 7);
    assert(proj(t[j], cols)[0] == t[j][0]);
    assert(proj(t[j], cols)[1] == t[j][1]);
    assert(proj(t[j], cols)[4] == t[j][4]);
    assert(proj(t[j], cols)[7] == t[j][7]);
    let cs = oid::stored_columns_t0();
    oid::lemma_stored_relations(db);
    assert(value_in_column(rels[0][j][4], cs[4]));
    assert(crate::spec::limits::date_min() == -2451545) by (compute);
}

/// Customer row `r`: arity, `c_custkey`, `c_mktsegment`.
pub proof fn lemma_customer_row(sv: StoresView, db: Database, r: int)
    requires bound_db(sv, db), 0 <= r < db.tables[2].len(),
    ensures
        db.tables[2][r].len() == 8,
        db.tables[2][r][0] == Val::Int(ck(sv)[r] as int),
        db.tables[2][r][6] == Val::Text(cseg(sv, r)),
{
    lemma_parts_shape(sv, db);
    cid::lemma_declared_schema();
    let t = db.tables[2];
    let cols = cid::stored_cols_t0();
    let rels = cid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][r] == ci::row_at(sv.flat_customer, r));
    assert(rels[0][r] == proj(t[r], cols));
    assert(row_in_table(t[r], db.schema[2]));
    assert(cols[0] == 0 && cols[6] == 6);
    assert(proj(t[r], cols)[0] == t[r][0]);
    assert(proj(t[r], cols)[6] == t[r][6]);
}

} // verus!
