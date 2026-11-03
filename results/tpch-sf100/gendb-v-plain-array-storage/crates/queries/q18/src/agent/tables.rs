//! Column views of the three flat storages the query reads (`flat_lineitem`, `flat_orders`, `flat_customer`) and
//! how they denote the database tables.
//!
//! Every column the query touches is one stored part (a plain array in source row order): `lk(sv)[i]` is
//! `l_orderkey` of lineitem row `i`, `lq(sv)[i]` its `l_quantity` coefficient (scale 2), `ok/oc/otp/od(sv)[j]` the
//! orders row `j`'s key, customer key, total price coefficient (scale 2) and date (days since 1970-01-01),
//! `ck(sv)[a]` and `cname(sv, a)` customer row `a`'s key and name bytes. For a database bound to the parts
//! (`bound_db`), the `lemma_*_row` lemmas state the values of one row at the table ordinals and their domains.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::typing::*;
use crate::spec::types::*;
use crate::spec::constraints::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::gendb_constraints::declared_db;
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::link::query::{text_at, TextView, proj};
use crate::link::source::lemma_proj_all_index;
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

/// `l_quantity` coefficients (scale 2).
pub open spec fn lq(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_QUANTITY as int]) }

/// `o_orderkey` of every orders row.
pub open spec fn ok(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_ORDERKEY as int]) }

/// `o_custkey` of every orders row.
pub open spec fn oc(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_CUSTKEY as int]) }

/// `o_totalprice` coefficients (scale 2).
pub open spec fn otp(sv: StoresView) -> Seq<i128> { oi::i128s(sv.flat_orders[oi::O_TOTALPRICE as int]) }

/// `o_orderdate` of every orders row (days since 1970-01-01).
pub open spec fn od(sv: StoresView) -> Seq<i32> { oi::i32s(sv.flat_orders[oi::O_ORDERDATE as int]) }

/// `c_custkey` of every customer row.
pub open spec fn ck(sv: StoresView) -> Seq<i64> { ci::i64s(sv.flat_customer[ci::C_CUSTKEY as int]) }

/// The `c_name` text column (offsets and bytes parts).
pub open spec fn cname_col(sv: StoresView) -> TextView {
    ci::text_view(sv.flat_customer, ci::C_NAME_OFFSETS as int, ci::C_NAME_BYTES as int)
}

/// `c_name` of customer row `a` (its bytes).
pub open spec fn cname(sv: StoresView, a: int) -> Seq<u8> { text_at(cname_col(sv), a) }

/// Row counts of the three tables.
pub open spec fn n_l(sv: StoresView) -> int { lk(sv).len() as int }
pub open spec fn n_o(sv: StoresView) -> int { ok(sv).len() as int }
pub open spec fn n_c(sv: StoresView) -> int { ck(sv).len() as int }

/// The parts have the shape of the three flat storages (a consequence of `bound_db`, `lemma_parts_shape`).
pub open spec fn parts_shape(sv: StoresView) -> bool {
    &&& li::parts_wf(sv.flat_lineitem, n_l(sv))
    &&& oi::parts_wf(sv.flat_orders, n_o(sv))
    &&& ci::parts_wf(sv.flat_customer, n_c(sv))
}

/// Values of the declared numeric(15,2) columns: `|coefficient| < 10^15`.
pub open spec fn num15(c: i128) -> bool { -1_000_000_000_000_000 < c < 1_000_000_000_000_000 }

/// The values of a key column are pairwise distinct.
pub open spec fn keys_unique(s: Seq<i64>) -> bool {
    forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && #[trigger] s[a] == #[trigger] s[b] ==> a == b
}

/// Every fact about the stored columns the executable code relies on.
pub open spec fn cols_facts(sv: StoresView) -> bool {
    &&& parts_shape(sv)
    &&& lq(sv).len() == n_l(sv)
    &&& oc(sv).len() == n_o(sv) && otp(sv).len() == n_o(sv) && od(sv).len() == n_o(sv)
    &&& keys_unique(ok(sv)) && keys_unique(ck(sv))
    &&& forall|i: int| 0 <= i < n_l(sv) ==> num15(#[trigger] lq(sv)[i])
    &&& forall|j: int| 0 <= j < n_o(sv) ==> num15(#[trigger] otp(sv)[j])
    &&& forall|j: int| 0 <= j < n_o(sv) ==> #[trigger] od(sv)[j] as int - 10957 >= -2451545
}

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
        lq(sv).len() == n_l(sv),
        oc(sv).len() == n_o(sv), otp(sv).len() == n_o(sv), od(sv).len() == n_o(sv),
{
    lid::lemma_declared_schema();
    lemma_proj_all_index(db.tables[0], lid::stored_cols_t0());
    lemma_proj_all_index(db.tables[1], oid::stored_cols_t0());
    lemma_proj_all_index(db.tables[2], cid::stored_cols_t0());
    assert(lid::stored_relations(db)[0].len() == db.tables[0].len());
    assert(oid::stored_relations(db)[0].len() == db.tables[1].len());
    assert(cid::stored_relations(db)[0].len() == db.tables[2].len());
}

/// Lineitem row `i`: arity, `l_orderkey`, `l_quantity` and its numeric(15,2) bound.
pub proof fn lemma_lineitem_row(sv: StoresView, db: Database, i: int)
    requires bound_db(sv, db), 0 <= i < db.tables[0].len(),
    ensures
        db.tables[0][i].len() == 16,
        db.tables[0][i][0] == Val::Int(lk(sv)[i] as int),
        db.tables[0][i][4] == (Val::Num { coeff: lq(sv)[i] as int, scale: 2 }),
        num15(lq(sv)[i]),
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
    assert(cols[0] == 0 && cols[4] == 4);
    assert(proj(t[i], cols)[0] == t[i][0]);
    assert(proj(t[i], cols)[4] == t[i][4]);
    let cs = lid::stored_columns_t0();
    assert(value_in_column(rels[0][i][4], cs[4]));
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
}

/// Orders row `j`: arity, `o_orderkey`, `o_custkey`, `o_totalprice`, `o_orderdate` and their domains.
pub proof fn lemma_orders_row(sv: StoresView, db: Database, j: int)
    requires bound_db(sv, db), 0 <= j < db.tables[1].len(),
    ensures
        db.tables[1][j].len() == 9,
        db.tables[1][j][0] == Val::Int(ok(sv)[j] as int),
        db.tables[1][j][1] == Val::Int(oc(sv)[j] as int),
        db.tables[1][j][3] == (Val::Num { coeff: otp(sv)[j] as int, scale: 2 }),
        db.tables[1][j][4] == date32_val(od(sv)[j]),
        num15(otp(sv)[j]),
        od(sv)[j] as int - 10957 >= -2451545,
{
    lemma_parts_shape(sv, db);
    oid::lemma_declared_schema();
    oid::lemma_stored_relations(db);
    let t = db.tables[1];
    let cols = oid::stored_cols_t0();
    let rels = oid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][j] == oi::row_at(sv.flat_orders, j));
    assert(rels[0][j] == proj(t[j], cols));
    assert(row_in_table(t[j], db.schema[1]));
    assert(cols[0] == 0 && cols[1] == 1 && cols[3] == 3 && cols[4] == 4);
    assert(proj(t[j], cols)[0] == t[j][0]);
    assert(proj(t[j], cols)[1] == t[j][1]);
    assert(proj(t[j], cols)[3] == t[j][3]);
    assert(proj(t[j], cols)[4] == t[j][4]);
    let cs = oid::stored_columns_t0();
    assert(value_in_column(rels[0][j][3], cs[3]));
    assert(value_in_column(rels[0][j][4], cs[4]));
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
    assert(crate::spec::limits::date_min() == -2451545) by (compute);
}

/// Customer row `a`: arity, `c_custkey`, `c_name`.
pub proof fn lemma_customer_row(sv: StoresView, db: Database, a: int)
    requires bound_db(sv, db), 0 <= a < db.tables[2].len(),
    ensures
        db.tables[2][a].len() == 8,
        db.tables[2][a][0] == Val::Int(ck(sv)[a] as int),
        db.tables[2][a][1] == Val::Text(cname(sv, a)),
{
    lemma_parts_shape(sv, db);
    cid::lemma_declared_schema();
    let t = db.tables[2];
    let cols = cid::stored_cols_t0();
    let rels = cid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][a] == ci::row_at(sv.flat_customer, a));
    assert(rels[0][a] == proj(t[a], cols));
    assert(row_in_table(t[a], db.schema[2]));
    assert(cols[0] == 0 && cols[1] == 1);
    assert(proj(t[a], cols)[0] == t[a][0]);
    assert(proj(t[a], cols)[1] == t[a][1]);
}

/// PRIMARY KEY (o_orderkey) and PRIMARY KEY (c_custkey): the stored key columns of a bound database are unique.
pub proof fn lemma_keys_unique(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures keys_unique(ok(sv)), keys_unique(ck(sv)),
{
    lemma_parts_shape(sv, db);
    let ddb = declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    let kcols = seq![0nat];
    assert(ddb.schema[1].constraints[0] == (Constraint::Key { cols: kcols, primary: true, nulls_distinct: true }));
    assert(ddb.schema[2].constraints[0] == (Constraint::Key { cols: kcols, primary: true, nulls_distinct: true }));
    assert forall|a: int, b: int| 0 <= a < ok(sv).len() && 0 <= b < ok(sv).len() && #[trigger] ok(sv)[a] == #[trigger] ok(sv)[b]
        implies a == b by {
        lemma_orders_row(sv, db, a);
        lemma_orders_row(sv, db, b);
        let ka = key_of(db.tables[1][a], kcols);
        let kb = key_of(db.tables[1][b], kcols);
        assert(ka[0] == db.tables[1][a][0]);
        assert(kb[0] == db.tables[1][b][0]);
        assert(crate::spec::equality::val_not_distinct(ka[0], kb[0]));
        assert(crate::spec::equality::row_not_distinct(ka, kb));
        lemma_primary_key_identifies(ddb, 1, 0, kcols, true, a, b);
    }
    assert forall|a: int, b: int| 0 <= a < ck(sv).len() && 0 <= b < ck(sv).len() && #[trigger] ck(sv)[a] == #[trigger] ck(sv)[b]
        implies a == b by {
        lemma_customer_row(sv, db, a);
        lemma_customer_row(sv, db, b);
        let ka = key_of(db.tables[2][a], kcols);
        let kb = key_of(db.tables[2][b], kcols);
        assert(ka[0] == db.tables[2][a][0]);
        assert(kb[0] == db.tables[2][b][0]);
        assert(crate::spec::equality::val_not_distinct(ka[0], kb[0]));
        assert(crate::spec::equality::row_not_distinct(ka, kb));
        lemma_primary_key_identifies(ddb, 2, 0, kcols, true, a, b);
    }
}

/// Every bound database gives the column facts.
pub proof fn lemma_cols_facts(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures cols_facts(sv),
{
    lemma_parts_shape(sv, db);
    lemma_keys_unique(sv, db);
    assert forall|i: int| 0 <= i < n_l(sv) implies num15(#[trigger] lq(sv)[i]) by {
        lemma_lineitem_row(sv, db, i);
    }
    assert forall|j: int| 0 <= j < n_o(sv) implies num15(#[trigger] otp(sv)[j]) by {
        lemma_orders_row(sv, db, j);
    }
    assert forall|j: int| 0 <= j < n_o(sv) implies #[trigger] od(sv)[j] as int - 10957 >= -2451545 by {
        lemma_orders_row(sv, db, j);
    }
}

} // verus!
