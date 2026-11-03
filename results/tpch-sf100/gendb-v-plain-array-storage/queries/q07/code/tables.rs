//! Column views of the five flat storages the query reads (`flat_lineitem`, `flat_orders`, `flat_customer`,
//! `flat_supplier`, `flat_nation`) and how they denote the database tables.
//!
//! Every column the query touches is one stored part (a plain array in source row order): `lsk(sv)[i]` is
//! `l_suppkey` of lineitem row `i`, `oc(sv)[j]` is `o_custkey` of orders row `j`, `lsd(sv)[i]` is `l_shipdate`
//! (days since 1970-01-01), and so on. For a database `db` bound to the parts (`bound_db`), row `i` of each table has
//! these values at the columns' table ordinals and every value lies in its declared domain (`db_wf`); the
//! `lemma_*_row` lemmas state exactly the facts the query needs, one row at a time. The declared primary keys make
//! the key columns of orders, customer, supplier and nation duplicate-free (`lemma_keys_unique`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::typing::*;
use crate::spec::types::*;
use crate::spec::constraints::*;
use crate::gendb_entry::stores::{StoresView, stored_ok};
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::gendb_constraints::declared_db;
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::link::query::{text_at, TextView, proj_all, proj};
use crate::link::source::lemma_proj_all_index;
use crate::schema::schema_spec;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_lineitem::declaration as lid;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_orders::declaration as oid;
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_customer::declaration as cid;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_supplier::declaration as sid;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_nation::declaration as nid;

verus! {

// ------------------------------------------------------------------------------------------------ column views

/// `l_orderkey` of every lineitem row.
pub open spec fn lok(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_ORDERKEY as int]) }

/// `l_suppkey` of every lineitem row.
pub open spec fn lsk(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_SUPPKEY as int]) }

/// `l_extendedprice` coefficients (scale 2).
pub open spec fn lpr(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_EXTENDEDPRICE as int]) }

/// `l_discount` coefficients (scale 2).
pub open spec fn ldc(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_DISCOUNT as int]) }

/// `l_shipdate` of every lineitem row (days since 1970-01-01).
pub open spec fn lsd(sv: StoresView) -> Seq<i32> { li::i32s(sv.flat_lineitem[li::L_SHIPDATE as int]) }

/// `o_orderkey` of every orders row.
pub open spec fn ok(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_ORDERKEY as int]) }

/// `o_custkey` of every orders row.
pub open spec fn oc(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_CUSTKEY as int]) }

/// `c_custkey` of every customer row.
pub open spec fn ck(sv: StoresView) -> Seq<i64> { ci::i64s(sv.flat_customer[ci::C_CUSTKEY as int]) }

/// `c_nationkey` of every customer row.
pub open spec fn cn(sv: StoresView) -> Seq<i64> { ci::i64s(sv.flat_customer[ci::C_NATIONKEY as int]) }

/// `s_suppkey` of every supplier row.
pub open spec fn sk(sv: StoresView) -> Seq<i64> { si::i64s(sv.flat_supplier[si::S_SUPPKEY as int]) }

/// `s_nationkey` of every supplier row.
pub open spec fn sn(sv: StoresView) -> Seq<i64> { si::i64s(sv.flat_supplier[si::S_NATIONKEY as int]) }

/// `n_nationkey` of every nation row.
pub open spec fn nk(sv: StoresView) -> Seq<i64> { ni::i64s(sv.flat_nation[ni::N_NATIONKEY as int]) }

/// The `n_name` text column (offsets and bytes parts).
pub open spec fn nname_col(sv: StoresView) -> TextView {
    ni::text_view(sv.flat_nation, ni::N_NAME_OFFSETS as int, ni::N_NAME_BYTES as int)
}

/// `n_name` of nation row `a` (its bytes).
pub open spec fn nname(sv: StoresView, a: int) -> Seq<u8> { text_at(nname_col(sv), a) }

/// Row counts of the five tables.
pub open spec fn n_l(sv: StoresView) -> int { lok(sv).len() as int }
pub open spec fn n_o(sv: StoresView) -> int { ok(sv).len() as int }
pub open spec fn n_c(sv: StoresView) -> int { ck(sv).len() as int }
pub open spec fn n_s(sv: StoresView) -> int { sk(sv).len() as int }
pub open spec fn n_n(sv: StoresView) -> int { nk(sv).len() as int }

/// The parts have the shape of the five flat storages: every column the query reads has one value per row, and
/// the name text column is well formed. (A consequence of `bound_db`, `lemma_parts_shape`.)
pub open spec fn parts_shape(sv: StoresView) -> bool {
    &&& li::parts_wf(sv.flat_lineitem, n_l(sv))
    &&& oi::parts_wf(sv.flat_orders, n_o(sv))
    &&& ci::parts_wf(sv.flat_customer, n_c(sv))
    &&& si::parts_wf(sv.flat_supplier, n_s(sv))
    &&& ni::parts_wf(sv.flat_nation, n_n(sv))
}

/// Values of the declared numeric(15,2) columns: `|coefficient| < 10^15`.
pub open spec fn num15(c: i128) -> bool { -1_000_000_000_000_000 < c < 1_000_000_000_000_000 }

/// The values of a key column are pairwise distinct.
pub open spec fn keys_unique(s: Seq<i64>) -> bool {
    forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && #[trigger] s[a] == #[trigger] s[b] ==> a == b
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
        db.tables[5].len() == n_s(sv),
        db.tables[6].len() == n_n(sv),
        lsk(sv).len() == n_l(sv), lpr(sv).len() == n_l(sv), ldc(sv).len() == n_l(sv), lsd(sv).len() == n_l(sv),
        oc(sv).len() == n_o(sv), cn(sv).len() == n_c(sv), sn(sv).len() == n_s(sv),
{
    lid::lemma_declared_schema();
    lemma_proj_all_index(db.tables[0], lid::stored_cols_t0());
    lemma_proj_all_index(db.tables[1], oid::stored_cols_t0());
    lemma_proj_all_index(db.tables[2], cid::stored_cols_t0());
    lemma_proj_all_index(db.tables[5], sid::stored_cols_t0());
    lemma_proj_all_index(db.tables[6], nid::stored_cols_t0());
    assert(lid::stored_relations(db)[0].len() == db.tables[0].len());
    assert(oid::stored_relations(db)[0].len() == db.tables[1].len());
    assert(cid::stored_relations(db)[0].len() == db.tables[2].len());
    assert(sid::stored_relations(db)[0].len() == db.tables[5].len());
    assert(nid::stored_relations(db)[0].len() == db.tables[6].len());
}

/// Lineitem row `i`: arity, `l_orderkey`, `l_suppkey`, `l_extendedprice`, `l_discount`, `l_shipdate`, and the
/// numeric bounds.
pub proof fn lemma_lineitem_row(sv: StoresView, db: Database, i: int)
    requires bound_db(sv, db), 0 <= i < n_l(sv),
    ensures
        db.tables[0][i].len() == 16,
        db.tables[0][i][0] == Val::Int(lok(sv)[i] as int),
        db.tables[0][i][2] == Val::Int(lsk(sv)[i] as int),
        db.tables[0][i][5] == (Val::Num { coeff: lpr(sv)[i] as int, scale: 2 }),
        db.tables[0][i][6] == (Val::Num { coeff: ldc(sv)[i] as int, scale: 2 }),
        db.tables[0][i][10] == date32_val(lsd(sv)[i]),
        num15(lpr(sv)[i]),
        num15(ldc(sv)[i]),
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
    assert(cols[0] == 0 && cols[2] == 2 && cols[5] == 5 && cols[6] == 6 && cols[10] == 10);
    assert(proj(t[i], cols)[0] == t[i][0]);
    assert(proj(t[i], cols)[2] == t[i][2]);
    assert(proj(t[i], cols)[5] == t[i][5]);
    assert(proj(t[i], cols)[6] == t[i][6]);
    assert(proj(t[i], cols)[10] == t[i][10]);
    let cs = lid::stored_columns_t0();
    assert(value_in_column(rels[0][i][5], cs[5]));
    assert(value_in_column(rels[0][i][6], cs[6]));
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
}

/// Orders row `j`: arity, `o_orderkey`, `o_custkey`.
pub proof fn lemma_orders_row(sv: StoresView, db: Database, j: int)
    requires bound_db(sv, db), 0 <= j < n_o(sv),
    ensures
        db.tables[1][j].len() == 9,
        db.tables[1][j][0] == Val::Int(ok(sv)[j] as int),
        db.tables[1][j][1] == Val::Int(oc(sv)[j] as int),
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
    assert(cols[0] == 0 && cols[1] == 1);
    assert(proj(t[j], cols)[0] == t[j][0]);
    assert(proj(t[j], cols)[1] == t[j][1]);
}

/// Customer row `r`: arity, `c_custkey`, `c_nationkey`.
pub proof fn lemma_customer_row(sv: StoresView, db: Database, r: int)
    requires bound_db(sv, db), 0 <= r < n_c(sv),
    ensures
        db.tables[2][r].len() == 8,
        db.tables[2][r][0] == Val::Int(ck(sv)[r] as int),
        db.tables[2][r][3] == Val::Int(cn(sv)[r] as int),
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
    assert(cols[0] == 0 && cols[3] == 3);
    assert(proj(t[r], cols)[0] == t[r][0]);
    assert(proj(t[r], cols)[3] == t[r][3]);
}

/// Supplier row `s`: arity, `s_suppkey`, `s_nationkey`.
pub proof fn lemma_supplier_row(sv: StoresView, db: Database, s: int)
    requires bound_db(sv, db), 0 <= s < n_s(sv),
    ensures
        db.tables[5][s].len() == 7,
        db.tables[5][s][0] == Val::Int(sk(sv)[s] as int),
        db.tables[5][s][3] == Val::Int(sn(sv)[s] as int),
{
    lemma_parts_shape(sv, db);
    sid::lemma_declared_schema();
    let t = db.tables[5];
    let cols = sid::stored_cols_t0();
    let rels = sid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][s] == si::row_at(sv.flat_supplier, s));
    assert(rels[0][s] == proj(t[s], cols));
    assert(row_in_table(t[s], db.schema[5]));
    assert(cols[0] == 0 && cols[3] == 3);
    assert(proj(t[s], cols)[0] == t[s][0]);
    assert(proj(t[s], cols)[3] == t[s][3]);
}

/// Nation row `a`: arity, `n_nationkey`, `n_name`.
pub proof fn lemma_nation_row(sv: StoresView, db: Database, a: int)
    requires bound_db(sv, db), 0 <= a < n_n(sv),
    ensures
        db.tables[6][a].len() == 4,
        db.tables[6][a][0] == Val::Int(nk(sv)[a] as int),
        db.tables[6][a][1] == Val::Text(nname(sv, a)),
{
    lemma_parts_shape(sv, db);
    nid::lemma_declared_schema();
    let t = db.tables[6];
    let cols = nid::stored_cols_t0();
    let rels = nid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][a] == ni::row_at(sv.flat_nation, a));
    assert(rels[0][a] == proj(t[a], cols));
    assert(row_in_table(t[a], db.schema[6]));
    assert(cols[0] == 0 && cols[1] == 1);
    assert(proj(t[a], cols)[0] == t[a][0]);
    assert(proj(t[a], cols)[1] == t[a][1]);
}

// ------------------------------------------------------------------------------------------------ primary keys

/// A single-column PRIMARY KEY (constraint 0 of table `t`) of a bound database: two rows whose key cells are the
/// same integer are the same row.
proof fn lemma_pk_rows(db: Database, t: int, a: int, b: int, x: int)
    requires
        constraints_hold(declared_db(db)), db.tables.len() == 8, 0 <= t < 8,
        declared_db(db).schema[t].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }),
        0 <= a < db.tables[t].len(), 0 <= b < db.tables[t].len(),
        db.tables[t][a].len() > 0, db.tables[t][b].len() > 0,
        db.tables[t][a][0] == Val::Int(x), db.tables[t][b][0] == Val::Int(x),
    ensures a == b,
{
    let ddb = declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    lid::lemma_declared_schema();
    let kcols = seq![0nat];
    let ka = key_of(db.tables[t][a], kcols);
    let kb = key_of(db.tables[t][b], kcols);
    assert(ka[0] == db.tables[t][a][0]);
    assert(kb[0] == db.tables[t][b][0]);
    assert(crate::spec::equality::val_not_distinct(ka[0], kb[0]));
    assert(crate::spec::equality::row_not_distinct(ka, kb));
    lemma_primary_key_identifies(ddb, t, 0, kcols, true, a, b);
}

/// PRIMARY KEY (o_orderkey), (c_custkey), (s_suppkey), (n_nationkey): the stored key columns of a bound database
/// are duplicate-free.
pub proof fn lemma_keys_unique(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures keys_unique(ok(sv)), keys_unique(ck(sv)), keys_unique(sk(sv)), keys_unique(nk(sv)),
{
    lemma_parts_shape(sv, db);
    crate::gendb_constraints::lemma_declared_schema();
    let ddb = declared_db(db);
    let pk = Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true };
    assert(ddb.schema[1].constraints[0] == pk);
    assert(ddb.schema[2].constraints[0] == pk);
    assert(ddb.schema[5].constraints[0] == pk);
    assert(ddb.schema[6].constraints[0] == pk);
    assert forall|a: int, b: int| 0 <= a < ok(sv).len() && 0 <= b < ok(sv).len() && #[trigger] ok(sv)[a] == #[trigger] ok(sv)[b]
        implies a == b by {
        lemma_orders_row(sv, db, a);
        lemma_orders_row(sv, db, b);
        lemma_pk_rows(db, 1, a, b, ok(sv)[a] as int);
    }
    assert forall|a: int, b: int| 0 <= a < ck(sv).len() && 0 <= b < ck(sv).len() && #[trigger] ck(sv)[a] == #[trigger] ck(sv)[b]
        implies a == b by {
        lemma_customer_row(sv, db, a);
        lemma_customer_row(sv, db, b);
        lemma_pk_rows(db, 2, a, b, ck(sv)[a] as int);
    }
    assert forall|a: int, b: int| 0 <= a < sk(sv).len() && 0 <= b < sk(sv).len() && #[trigger] sk(sv)[a] == #[trigger] sk(sv)[b]
        implies a == b by {
        lemma_supplier_row(sv, db, a);
        lemma_supplier_row(sv, db, b);
        lemma_pk_rows(db, 5, a, b, sk(sv)[a] as int);
    }
    assert forall|a: int, b: int| 0 <= a < nk(sv).len() && 0 <= b < nk(sv).len() && #[trigger] nk(sv)[a] == #[trigger] nk(sv)[b]
        implies a == b by {
        lemma_nation_row(sv, db, a);
        lemma_nation_row(sv, db, b);
        lemma_pk_rows(db, 6, a, b, nk(sv)[a] as int);
    }
}

} // verus!
