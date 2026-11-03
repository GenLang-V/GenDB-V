//! Column views of the six flat storages the query reads (`flat_lineitem`, `flat_orders`, `flat_part`,
//! `flat_partsupp`, `flat_supplier`, `flat_nation`) and how they denote the database tables.
//!
//! Every column the query touches is one stored part (a plain array in source row order): `lpk(sv)[i]` is
//! `l_partkey` of lineitem row `i`, `od(sv)[j]` is `o_orderdate` of orders row `j` (days since 1970-01-01),
//! `pname(sv, p)` the bytes of `p_name` of part row `p`, and so on. For a database `db` bound to the parts
//! (`bound_db`), row `i` of each table has these values at the columns' table ordinals and every value lies in its
//! declared domain (`db_wf`); the `lemma_*_row` lemmas state exactly the facts the query needs, one row at a time.
//! The declared primary keys make the key columns of part, supplier, orders and nation, and the key pair
//! `(ps_partkey, ps_suppkey)` of partsupp, duplicate-free (`lemma_keys_unique`).
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
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_part::declaration as pid;
use crate::stores::flat_partsupp::interface as psi;
use crate::stores::flat_partsupp::declaration as psid;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_supplier::declaration as sid;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_nation::declaration as nid;

verus! {

// ------------------------------------------------------------------------------------------------ column views

/// `l_orderkey` of every lineitem row.
pub open spec fn lok(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_ORDERKEY as int]) }

/// `l_partkey` of every lineitem row.
pub open spec fn lpk(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_PARTKEY as int]) }

/// `l_suppkey` of every lineitem row.
pub open spec fn lsk(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_SUPPKEY as int]) }

/// `l_quantity` coefficients (scale 2).
pub open spec fn lqt(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_QUANTITY as int]) }

/// `l_extendedprice` coefficients (scale 2).
pub open spec fn lpr(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_EXTENDEDPRICE as int]) }

/// `l_discount` coefficients (scale 2).
pub open spec fn ldc(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_DISCOUNT as int]) }

/// `o_orderkey` of every orders row.
pub open spec fn ok(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_ORDERKEY as int]) }

/// `o_orderdate` of every orders row (days since 1970-01-01).
pub open spec fn od(sv: StoresView) -> Seq<i32> { oi::i32s(sv.flat_orders[oi::O_ORDERDATE as int]) }

/// `p_partkey` of every part row.
pub open spec fn pk(sv: StoresView) -> Seq<i64> { pi::i64s(sv.flat_part[pi::P_PARTKEY as int]) }

/// The `p_name` text column (offsets and bytes parts).
pub open spec fn pname_col(sv: StoresView) -> TextView {
    pi::text_view(sv.flat_part, pi::P_NAME_OFFSETS as int, pi::P_NAME_BYTES as int)
}

/// `p_name` of part row `p` (its bytes).
pub open spec fn pname(sv: StoresView, p: int) -> Seq<u8> { text_at(pname_col(sv), p) }

/// `ps_partkey` of every partsupp row.
pub open spec fn pspk(sv: StoresView) -> Seq<i64> { psi::i64s(sv.flat_partsupp[psi::PS_PARTKEY as int]) }

/// `ps_suppkey` of every partsupp row.
pub open spec fn pssk(sv: StoresView) -> Seq<i64> { psi::i64s(sv.flat_partsupp[psi::PS_SUPPKEY as int]) }

/// `ps_supplycost` coefficients (scale 2).
pub open spec fn psc(sv: StoresView) -> Seq<i128> { psi::i128s(sv.flat_partsupp[psi::PS_SUPPLYCOST as int]) }

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

/// Row counts of the six tables.
pub open spec fn n_l(sv: StoresView) -> int { lok(sv).len() as int }
pub open spec fn n_o(sv: StoresView) -> int { ok(sv).len() as int }
pub open spec fn n_p(sv: StoresView) -> int { pk(sv).len() as int }
pub open spec fn n_ps(sv: StoresView) -> int { pspk(sv).len() as int }
pub open spec fn n_s(sv: StoresView) -> int { sk(sv).len() as int }
pub open spec fn n_n(sv: StoresView) -> int { nk(sv).len() as int }

/// The parts have the shape of the six flat storages: every column the query reads has one value per row, and
/// the name text columns are well formed. (A consequence of `bound_db`, `lemma_parts_shape`.)
pub open spec fn parts_shape(sv: StoresView) -> bool {
    &&& li::parts_wf(sv.flat_lineitem, n_l(sv))
    &&& oi::parts_wf(sv.flat_orders, n_o(sv))
    &&& pi::parts_wf(sv.flat_part, n_p(sv))
    &&& psi::parts_wf(sv.flat_partsupp, n_ps(sv))
    &&& si::parts_wf(sv.flat_supplier, n_s(sv))
    &&& ni::parts_wf(sv.flat_nation, n_n(sv))
}

/// The column lengths implied by `parts_shape`.
pub open spec fn col_lens(sv: StoresView) -> bool {
    &&& lpk(sv).len() == n_l(sv) && lsk(sv).len() == n_l(sv)
    &&& lqt(sv).len() == n_l(sv) && lpr(sv).len() == n_l(sv) && ldc(sv).len() == n_l(sv)
    &&& od(sv).len() == n_o(sv)
    &&& pssk(sv).len() == n_ps(sv) && psc(sv).len() == n_ps(sv)
    &&& sn(sv).len() == n_s(sv)
}

/// Values of the declared numeric(15,2) columns: `|coefficient| < 10^15`.
pub open spec fn num15(c: i128) -> bool { -1_000_000_000_000_000 < c < 1_000_000_000_000_000 }

/// The values of a key column are pairwise distinct.
pub open spec fn keys_unique(s: Seq<i64>) -> bool {
    forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && #[trigger] s[a] == #[trigger] s[b] ==> a == b
}

/// The value pairs of two key columns of one length are pairwise distinct.
pub open spec fn keys2_unique(s: Seq<i64>, t: Seq<i64>) -> bool {
    forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && #[trigger] s[a] == #[trigger] s[b] && t[a] == t[b] ==> a == b
}

/// The numeric columns the query reads are inside numeric(15,2).
pub open spec fn nums_ok(sv: StoresView) -> bool {
    &&& forall|l: int| 0 <= l < n_l(sv) ==> num15(#[trigger] lqt(sv)[l]) && num15(lpr(sv)[l]) && num15(ldc(sv)[l])
    &&& forall|q: int| 0 <= q < n_ps(sv) ==> num15(#[trigger] psc(sv)[q])
}

// ------------------------------------------------------------------------------------------------ table facts

/// The parts of a bound database have the storages' shape, and the tables have the parts' row counts.
pub proof fn lemma_parts_shape(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        parts_shape(sv),
        col_lens(sv),
        db.tables.len() == 8,
        db.tables[0].len() == n_l(sv),
        db.tables[1].len() == n_o(sv),
        db.tables[3].len() == n_p(sv),
        db.tables[4].len() == n_ps(sv),
        db.tables[5].len() == n_s(sv),
        db.tables[6].len() == n_n(sv),
{
    lid::lemma_declared_schema();
    lemma_proj_all_index(db.tables[0], lid::stored_cols_t0());
    lemma_proj_all_index(db.tables[1], oid::stored_cols_t0());
    lemma_proj_all_index(db.tables[3], pid::stored_cols_t0());
    lemma_proj_all_index(db.tables[4], psid::stored_cols_t0());
    lemma_proj_all_index(db.tables[5], sid::stored_cols_t0());
    lemma_proj_all_index(db.tables[6], nid::stored_cols_t0());
    assert(lid::stored_relations(db)[0].len() == db.tables[0].len());
    assert(oid::stored_relations(db)[0].len() == db.tables[1].len());
    assert(pid::stored_relations(db)[0].len() == db.tables[3].len());
    assert(psid::stored_relations(db)[0].len() == db.tables[4].len());
    assert(sid::stored_relations(db)[0].len() == db.tables[5].len());
    assert(nid::stored_relations(db)[0].len() == db.tables[6].len());
}

/// Lineitem row `i`: arity, the keys, the three numeric columns and their bounds.
pub proof fn lemma_lineitem_row(sv: StoresView, db: Database, i: int)
    requires bound_db(sv, db), 0 <= i < n_l(sv),
    ensures
        db.tables[0][i].len() == 16,
        db.tables[0][i][0] == Val::Int(lok(sv)[i] as int),
        db.tables[0][i][1] == Val::Int(lpk(sv)[i] as int),
        db.tables[0][i][2] == Val::Int(lsk(sv)[i] as int),
        db.tables[0][i][4] == (Val::Num { coeff: lqt(sv)[i] as int, scale: 2 }),
        db.tables[0][i][5] == (Val::Num { coeff: lpr(sv)[i] as int, scale: 2 }),
        db.tables[0][i][6] == (Val::Num { coeff: ldc(sv)[i] as int, scale: 2 }),
        num15(lqt(sv)[i]),
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
    assert(cols[0] == 0 && cols[1] == 1 && cols[2] == 2 && cols[4] == 4 && cols[5] == 5 && cols[6] == 6);
    assert(proj(t[i], cols)[0] == t[i][0]);
    assert(proj(t[i], cols)[1] == t[i][1]);
    assert(proj(t[i], cols)[2] == t[i][2]);
    assert(proj(t[i], cols)[4] == t[i][4]);
    assert(proj(t[i], cols)[5] == t[i][5]);
    assert(proj(t[i], cols)[6] == t[i][6]);
    let cs = lid::stored_columns_t0();
    assert(value_in_column(rels[0][i][4], cs[4]));
    assert(value_in_column(rels[0][i][5], cs[5]));
    assert(value_in_column(rels[0][i][6], cs[6]));
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
}

/// Orders row `j`: arity, `o_orderkey`, `o_orderdate`.
pub proof fn lemma_orders_row(sv: StoresView, db: Database, j: int)
    requires bound_db(sv, db), 0 <= j < n_o(sv),
    ensures
        db.tables[1][j].len() == 9,
        db.tables[1][j][0] == Val::Int(ok(sv)[j] as int),
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
    assert(cols[0] == 0 && cols[4] == 4);
    assert(proj(t[j], cols)[0] == t[j][0]);
    assert(proj(t[j], cols)[4] == t[j][4]);
}

/// Part row `p`: arity, `p_partkey`, `p_name`.
pub proof fn lemma_part_row(sv: StoresView, db: Database, p: int)
    requires bound_db(sv, db), 0 <= p < n_p(sv),
    ensures
        db.tables[3][p].len() == 9,
        db.tables[3][p][0] == Val::Int(pk(sv)[p] as int),
        db.tables[3][p][1] == Val::Text(pname(sv, p)),
{
    lemma_parts_shape(sv, db);
    pid::lemma_declared_schema();
    let t = db.tables[3];
    let cols = pid::stored_cols_t0();
    let rels = pid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][p] == pi::row_at(sv.flat_part, p));
    assert(rels[0][p] == proj(t[p], cols));
    assert(row_in_table(t[p], db.schema[3]));
    assert(cols[0] == 0 && cols[1] == 1);
    assert(proj(t[p], cols)[0] == t[p][0]);
    assert(proj(t[p], cols)[1] == t[p][1]);
}

/// Partsupp row `q`: arity, the key pair, `ps_supplycost` and its bound.
pub proof fn lemma_partsupp_row(sv: StoresView, db: Database, q: int)
    requires bound_db(sv, db), 0 <= q < n_ps(sv),
    ensures
        db.tables[4][q].len() == 5,
        db.tables[4][q][0] == Val::Int(pspk(sv)[q] as int),
        db.tables[4][q][1] == Val::Int(pssk(sv)[q] as int),
        db.tables[4][q][3] == (Val::Num { coeff: psc(sv)[q] as int, scale: 2 }),
        num15(psc(sv)[q]),
{
    lemma_parts_shape(sv, db);
    psid::lemma_declared_schema();
    psid::lemma_stored_relations(db);
    let t = db.tables[4];
    let cols = psid::stored_cols_t0();
    let rels = psid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][q] == psi::row_at(sv.flat_partsupp, q));
    assert(rels[0][q] == proj(t[q], cols));
    assert(row_in_table(t[q], db.schema[4]));
    assert(cols[0] == 0 && cols[1] == 1 && cols[3] == 3);
    assert(proj(t[q], cols)[0] == t[q][0]);
    assert(proj(t[q], cols)[1] == t[q][1]);
    assert(proj(t[q], cols)[3] == t[q][3]);
    let cs = psid::stored_columns_t0();
    assert(value_in_column(rels[0][q][3], cs[3]));
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
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

/// The numeric columns of a bound database are inside numeric(15,2).
pub proof fn lemma_nums_ok(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures nums_ok(sv),
{
    assert forall|l: int| 0 <= l < n_l(sv) implies num15(#[trigger] lqt(sv)[l]) && num15(lpr(sv)[l]) && num15(ldc(sv)[l]) by {
        lemma_lineitem_row(sv, db, l);
    }
    assert forall|q: int| 0 <= q < n_ps(sv) implies num15(#[trigger] psc(sv)[q]) by {
        lemma_partsupp_row(sv, db, q);
    }
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

/// The two-column PRIMARY KEY (ps_partkey, ps_suppkey) of partsupp: two rows with the same key pair are the same row.
proof fn lemma_pk2_rows(db: Database, a: int, b: int, x: int, y: int)
    requires
        constraints_hold(declared_db(db)), db.tables.len() == 8,
        declared_db(db).schema[4].constraints[0] == (Constraint::Key { cols: seq![0nat, 1nat], primary: true, nulls_distinct: true }),
        0 <= a < db.tables[4].len(), 0 <= b < db.tables[4].len(),
        db.tables[4][a].len() > 1, db.tables[4][b].len() > 1,
        db.tables[4][a][0] == Val::Int(x), db.tables[4][b][0] == Val::Int(x),
        db.tables[4][a][1] == Val::Int(y), db.tables[4][b][1] == Val::Int(y),
    ensures a == b,
{
    let ddb = declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    lid::lemma_declared_schema();
    let kcols = seq![0nat, 1nat];
    let ka = key_of(db.tables[4][a], kcols);
    let kb = key_of(db.tables[4][b], kcols);
    assert(ka[0] == db.tables[4][a][0] && ka[1] == db.tables[4][a][1]);
    assert(kb[0] == db.tables[4][b][0] && kb[1] == db.tables[4][b][1]);
    assert(crate::spec::equality::val_not_distinct(ka[0], kb[0]));
    assert(crate::spec::equality::val_not_distinct(ka[1], kb[1]));
    assert(crate::spec::equality::row_not_distinct(ka, kb));
    lemma_primary_key_identifies(ddb, 4, 0, kcols, true, a, b);
}

/// PRIMARY KEY (p_partkey), (s_suppkey), (o_orderkey), (n_nationkey), (ps_partkey, ps_suppkey): the stored key
/// columns of a bound database are duplicate-free.
pub proof fn lemma_keys_unique(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        keys_unique(pk(sv)), keys_unique(sk(sv)), keys_unique(ok(sv)), keys_unique(nk(sv)),
        keys2_unique(pspk(sv), pssk(sv)),
{
    lemma_parts_shape(sv, db);
    crate::gendb_constraints::lemma_declared_schema();
    let ddb = declared_db(db);
    let pk1 = Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true };
    assert(ddb.schema[1].constraints[0] == pk1);
    assert(ddb.schema[3].constraints[0] == pk1);
    assert(ddb.schema[5].constraints[0] == pk1);
    assert(ddb.schema[6].constraints[0] == pk1);
    assert(ddb.schema[4].constraints[0] == (Constraint::Key { cols: seq![0nat, 1nat], primary: true, nulls_distinct: true }));
    assert forall|a: int, b: int| 0 <= a < pk(sv).len() && 0 <= b < pk(sv).len() && #[trigger] pk(sv)[a] == #[trigger] pk(sv)[b]
        implies a == b by {
        lemma_part_row(sv, db, a);
        lemma_part_row(sv, db, b);
        lemma_pk_rows(db, 3, a, b, pk(sv)[a] as int);
    }
    assert forall|a: int, b: int| 0 <= a < sk(sv).len() && 0 <= b < sk(sv).len() && #[trigger] sk(sv)[a] == #[trigger] sk(sv)[b]
        implies a == b by {
        lemma_supplier_row(sv, db, a);
        lemma_supplier_row(sv, db, b);
        lemma_pk_rows(db, 5, a, b, sk(sv)[a] as int);
    }
    assert forall|a: int, b: int| 0 <= a < ok(sv).len() && 0 <= b < ok(sv).len() && #[trigger] ok(sv)[a] == #[trigger] ok(sv)[b]
        implies a == b by {
        lemma_orders_row(sv, db, a);
        lemma_orders_row(sv, db, b);
        lemma_pk_rows(db, 1, a, b, ok(sv)[a] as int);
    }
    assert forall|a: int, b: int| 0 <= a < nk(sv).len() && 0 <= b < nk(sv).len() && #[trigger] nk(sv)[a] == #[trigger] nk(sv)[b]
        implies a == b by {
        lemma_nation_row(sv, db, a);
        lemma_nation_row(sv, db, b);
        lemma_pk_rows(db, 6, a, b, nk(sv)[a] as int);
    }
    assert forall|a: int, b: int| 0 <= a < pspk(sv).len() && 0 <= b < pspk(sv).len() && #[trigger] pspk(sv)[a] == #[trigger] pspk(sv)[b]
        && pssk(sv)[a] == pssk(sv)[b] implies a == b by {
        lemma_partsupp_row(sv, db, a);
        lemma_partsupp_row(sv, db, b);
        lemma_pk2_rows(db, a, b, pspk(sv)[a] as int, pssk(sv)[a] as int);
    }
}

} // verus!
