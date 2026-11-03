//! Column views of the four flat storages Q10 reads (`flat_lineitem`, `flat_orders`, `flat_customer`,
//! `flat_nation`) and how they denote the database tables.
//!
//! Every column is one stored part (a plain array in source row order; a text column is an offsets part and a bytes
//! part). `lk(sv)[i]` is `l_orderkey` of lineitem row `i`, `od(sv)[j]` is `o_orderdate` of orders row `j` (days since
//! 1970-01-01), `cname(sv, r)` the bytes of `c_name` of customer row `r`, and so on. For a database bound to the
//! parts (`bound_db`), row `i` of a table has these values at the columns' table ordinals and every value lies in
//! its declared domain; the `lemma_*_row` lemmas state exactly the facts the query needs, one row at a time.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::typing::*;
use crate::spec::constraints::*;
use crate::spec::types::Constraint;
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
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_nation::declaration as nid;

verus! {

// ------------------------------------------------------------------------------------------------ lineitem

/// `l_orderkey` of every lineitem row.
pub open spec fn lk(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_ORDERKEY as int]) }

/// `l_extendedprice` coefficients (scale 2).
pub open spec fn lp(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_EXTENDEDPRICE as int]) }

/// `l_discount` coefficients (scale 2).
pub open spec fn ld(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_DISCOUNT as int]) }

/// The `l_returnflag` text column (offsets and bytes parts).
pub open spec fn rf_col(sv: StoresView) -> TextView {
    li::text_view(sv.flat_lineitem, li::L_RETURNFLAG_OFFSETS as int, li::L_RETURNFLAG_BYTES as int)
}

/// `l_returnflag` of lineitem row `i` (its bytes).
pub open spec fn rf(sv: StoresView, i: int) -> Seq<u8> { text_at(rf_col(sv), i) }

// ------------------------------------------------------------------------------------------------ orders

/// `o_orderkey` of every orders row.
pub open spec fn ok(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_ORDERKEY as int]) }

/// `o_custkey` of every orders row.
pub open spec fn oc(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_CUSTKEY as int]) }

/// `o_orderdate` of every orders row (days since 1970-01-01).
pub open spec fn od(sv: StoresView) -> Seq<i32> { oi::i32s(sv.flat_orders[oi::O_ORDERDATE as int]) }

// ------------------------------------------------------------------------------------------------ customer

/// `c_custkey` of every customer row.
pub open spec fn ck(sv: StoresView) -> Seq<i64> { ci::i64s(sv.flat_customer[ci::C_CUSTKEY as int]) }

/// `c_nationkey` of every customer row.
pub open spec fn cnk(sv: StoresView) -> Seq<i64> { ci::i64s(sv.flat_customer[ci::C_NATIONKEY as int]) }

/// `c_acctbal` coefficients (scale 2).
pub open spec fn cacct(sv: StoresView) -> Seq<i128> { ci::i128s(sv.flat_customer[ci::C_ACCTBAL as int]) }

/// The customer text columns `c_name`, `c_address`, `c_phone`, `c_comment`.
pub open spec fn cname_col(sv: StoresView) -> TextView {
    ci::text_view(sv.flat_customer, ci::C_NAME_OFFSETS as int, ci::C_NAME_BYTES as int)
}
pub open spec fn caddr_col(sv: StoresView) -> TextView {
    ci::text_view(sv.flat_customer, ci::C_ADDRESS_OFFSETS as int, ci::C_ADDRESS_BYTES as int)
}
pub open spec fn cphone_col(sv: StoresView) -> TextView {
    ci::text_view(sv.flat_customer, ci::C_PHONE_OFFSETS as int, ci::C_PHONE_BYTES as int)
}
pub open spec fn ccomm_col(sv: StoresView) -> TextView {
    ci::text_view(sv.flat_customer, ci::C_COMMENT_OFFSETS as int, ci::C_COMMENT_BYTES as int)
}

// ------------------------------------------------------------------------------------------------ nation

/// `n_nationkey` of every nation row.
pub open spec fn nk(sv: StoresView) -> Seq<i64> { ni::i64s(sv.flat_nation[ni::N_NATIONKEY as int]) }

/// The `n_name` text column.
pub open spec fn nname_col(sv: StoresView) -> TextView {
    ni::text_view(sv.flat_nation, ni::N_NAME_OFFSETS as int, ni::N_NAME_BYTES as int)
}

// ------------------------------------------------------------------------------------------------ shapes

/// Row counts of the four tables.
pub open spec fn n_l(sv: StoresView) -> int { lk(sv).len() as int }
pub open spec fn n_o(sv: StoresView) -> int { ok(sv).len() as int }
pub open spec fn n_c(sv: StoresView) -> int { ck(sv).len() as int }
pub open spec fn n_n(sv: StoresView) -> int { nk(sv).len() as int }

/// The parts have the shape of the four flat storages: every column has one value per row and every text column
/// is well formed. (A consequence of `bound_db`, `lemma_parts_shape`.)
pub open spec fn parts_shape(sv: StoresView) -> bool {
    &&& li::parts_wf(sv.flat_lineitem, n_l(sv))
    &&& oi::parts_wf(sv.flat_orders, n_o(sv))
    &&& ci::parts_wf(sv.flat_customer, n_c(sv))
    &&& ni::parts_wf(sv.flat_nation, n_n(sv))
}

/// Values of the declared numeric(15,2) columns: `|coefficient| < 10^15`.
pub open spec fn num15(c: i128) -> bool { -1_000_000_000_000_000 < c < 1_000_000_000_000_000 }

/// The parts of a bound database have the storages' shape, and the tables have the parts' row counts.
pub proof fn lemma_parts_shape(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        parts_shape(sv),
        db.tables.len() == 8,
        db.tables[0].len() == n_l(sv),
        db.tables[1].len() == n_o(sv),
        db.tables[2].len() == n_c(sv),
        db.tables[6].len() == n_n(sv),
        lp(sv).len() == n_l(sv), ld(sv).len() == n_l(sv),
        oc(sv).len() == n_o(sv), od(sv).len() == n_o(sv),
        cnk(sv).len() == n_c(sv), cacct(sv).len() == n_c(sv),
{
    lid::lemma_declared_schema();
    lemma_proj_all_index(db.tables[0], lid::stored_cols_t0());
    lemma_proj_all_index(db.tables[1], oid::stored_cols_t0());
    lemma_proj_all_index(db.tables[2], cid::stored_cols_t0());
    lemma_proj_all_index(db.tables[6], nid::stored_cols_t0());
    assert(lid::stored_relations(db)[0].len() == db.tables[0].len());
    assert(oid::stored_relations(db)[0].len() == db.tables[1].len());
    assert(cid::stored_relations(db)[0].len() == db.tables[2].len());
    assert(nid::stored_relations(db)[0].len() == db.tables[6].len());
}

// ------------------------------------------------------------------------------------------------ rows

/// Lineitem row `i`: arity, `l_orderkey`, `l_extendedprice`, `l_discount`, `l_returnflag`, and the numeric bounds.
pub proof fn lemma_lineitem_row(sv: StoresView, db: Database, i: int)
    requires bound_db(sv, db), 0 <= i < db.tables[0].len(),
    ensures
        db.tables[0][i].len() == 16,
        db.tables[0][i][0] == Val::Int(lk(sv)[i] as int),
        db.tables[0][i][5] == (Val::Num { coeff: lp(sv)[i] as int, scale: 2 }),
        db.tables[0][i][6] == (Val::Num { coeff: ld(sv)[i] as int, scale: 2 }),
        db.tables[0][i][8] == Val::Text(rf(sv, i)),
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
    assert(cols[0] == 0 && cols[5] == 5 && cols[6] == 6 && cols[8] == 8);
    assert(proj(t[i], cols)[0] == t[i][0]);
    assert(proj(t[i], cols)[5] == t[i][5]);
    assert(proj(t[i], cols)[6] == t[i][6]);
    assert(proj(t[i], cols)[8] == t[i][8]);
    let cs = lid::stored_columns_t0();
    assert(value_in_column(rels[0][i][5], cs[5]));
    assert(value_in_column(rels[0][i][6], cs[6]));
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
}

/// Orders row `j`: arity, `o_orderkey`, `o_custkey`, `o_orderdate`.
pub proof fn lemma_orders_row(sv: StoresView, db: Database, j: int)
    requires bound_db(sv, db), 0 <= j < db.tables[1].len(),
    ensures
        db.tables[1][j].len() == 9,
        db.tables[1][j][0] == Val::Int(ok(sv)[j] as int),
        db.tables[1][j][1] == Val::Int(oc(sv)[j] as int),
        db.tables[1][j][4] == date32_val(od(sv)[j]),
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
    assert(cols[0] == 0 && cols[1] == 1 && cols[4] == 4);
    assert(proj(t[j], cols)[0] == t[j][0]);
    assert(proj(t[j], cols)[1] == t[j][1]);
    assert(proj(t[j], cols)[4] == t[j][4]);
}

/// Customer row `r`: arity and the seven columns the statement reads.
pub proof fn lemma_customer_row(sv: StoresView, db: Database, r: int)
    requires bound_db(sv, db), 0 <= r < db.tables[2].len(),
    ensures
        db.tables[2][r].len() == 8,
        db.tables[2][r][0] == Val::Int(ck(sv)[r] as int),
        db.tables[2][r][1] == Val::Text(text_at(cname_col(sv), r)),
        db.tables[2][r][2] == Val::Text(text_at(caddr_col(sv), r)),
        db.tables[2][r][3] == Val::Int(cnk(sv)[r] as int),
        db.tables[2][r][4] == Val::Text(text_at(cphone_col(sv), r)),
        db.tables[2][r][5] == (Val::Num { coeff: cacct(sv)[r] as int, scale: 2 }),
        db.tables[2][r][7] == Val::Text(text_at(ccomm_col(sv), r)),
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
    assert(cols[0] == 0 && cols[1] == 1 && cols[2] == 2 && cols[3] == 3 && cols[4] == 4 && cols[5] == 5 && cols[7] == 7);
    assert(proj(t[r], cols)[0] == t[r][0]);
    assert(proj(t[r], cols)[1] == t[r][1]);
    assert(proj(t[r], cols)[2] == t[r][2]);
    assert(proj(t[r], cols)[3] == t[r][3]);
    assert(proj(t[r], cols)[4] == t[r][4]);
    assert(proj(t[r], cols)[5] == t[r][5]);
    assert(proj(t[r], cols)[7] == t[r][7]);
}

/// Nation row `n`: arity, `n_nationkey`, `n_name`.
pub proof fn lemma_nation_row(sv: StoresView, db: Database, n: int)
    requires bound_db(sv, db), 0 <= n < db.tables[6].len(),
    ensures
        db.tables[6][n].len() == 4,
        db.tables[6][n][0] == Val::Int(nk(sv)[n] as int),
        db.tables[6][n][1] == Val::Text(text_at(nname_col(sv), n)),
{
    lemma_parts_shape(sv, db);
    nid::lemma_declared_schema();
    let t = db.tables[6];
    let cols = nid::stored_cols_t0();
    let rels = nid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][n] == ni::row_at(sv.flat_nation, n));
    assert(rels[0][n] == proj(t[n], cols));
    assert(row_in_table(t[n], db.schema[6]));
    assert(cols[0] == 0 && cols[1] == 1);
    assert(proj(t[n], cols)[0] == t[n][0]);
    assert(proj(t[n], cols)[1] == t[n][1]);
}

// ------------------------------------------------------------------------------------------------ primary keys

/// The values of a key column are pairwise distinct.
pub open spec fn keys_unique(s: Seq<i64>) -> bool {
    forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && #[trigger] s[a] == #[trigger] s[b] ==> a == b
}

/// A single-column primary key of table `t` makes its stored key column unique, given each row's key value.
proof fn lemma_pk_unique(db: Database, t: int, s: Seq<i64>)
    requires
        constraints_hold(declared_db(db)),
        db.schema == crate::schema::schema_spec(),
        db.tables.len() == 8, 0 <= t < 8,
        crate::gendb_constraints::declared_schema()[t].constraints.len() > 0,
        crate::gendb_constraints::declared_schema()[t].constraints[0]
            == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }),
        s.len() == db.tables[t].len(),
        forall|i: int| 0 <= i < s.len() ==> (#[trigger] db.tables[t][i]).len() > 0 && db.tables[t][i][0] == Val::Int(s[i] as int),
    ensures keys_unique(s),
{
    let ddb = declared_db(db);
    let kcols = seq![0nat];
    crate::gendb_constraints::lemma_declared_schema();
    assert forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && #[trigger] s[a] == #[trigger] s[b] implies a == b by {
        let ka = key_of(db.tables[t][a], kcols);
        let kb = key_of(db.tables[t][b], kcols);
        assert(ka[0] == db.tables[t][a][0]);
        assert(kb[0] == db.tables[t][b][0]);
        assert(crate::spec::equality::val_not_distinct(ka[0], kb[0]));
        assert(crate::spec::equality::row_not_distinct(ka, kb));
        lemma_primary_key_identifies(ddb, t, 0, kcols, true, a, b);
    }
}

/// PRIMARY KEY (o_orderkey), (c_custkey) and (n_nationkey): the stored key columns of a bound database are unique.
pub proof fn lemma_keys_unique(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures keys_unique(ok(sv)), keys_unique(ck(sv)), keys_unique(nk(sv)),
{
    lemma_parts_shape(sv, db);
    crate::gendb_constraints::lemma_declared_schema();
    assert forall|j: int| 0 <= j < ok(sv).len() implies (#[trigger] db.tables[1][j]).len() > 0
        && db.tables[1][j][0] == Val::Int(ok(sv)[j] as int) by {
        lemma_orders_row(sv, db, j);
    }
    lemma_pk_unique(db, 1, ok(sv));
    assert forall|r: int| 0 <= r < ck(sv).len() implies (#[trigger] db.tables[2][r]).len() > 0
        && db.tables[2][r][0] == Val::Int(ck(sv)[r] as int) by {
        lemma_customer_row(sv, db, r);
    }
    lemma_pk_unique(db, 2, ck(sv));
    assert forall|n: int| 0 <= n < nk(sv).len() implies (#[trigger] db.tables[6][n]).len() > 0
        && db.tables[6][n][0] == Val::Int(nk(sv)[n] as int) by {
        lemma_nation_row(sv, db, n);
    }
    lemma_pk_unique(db, 6, nk(sv));
}

} // verus!
