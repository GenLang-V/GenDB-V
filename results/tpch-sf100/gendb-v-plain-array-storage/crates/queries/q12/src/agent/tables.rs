//! Column views of the two flat storages the query reads (`flat_lineitem`, `flat_orders`) and how they denote the
//! database tables.
//!
//! Every column the query touches is one stored part (a plain array in source row order): `lok(sv)[i]` is
//! `l_orderkey` of lineitem row `i`, `lrd(sv)[i]` its `l_receiptdate` (days since 1970-01-01), `lmode(sv)` the
//! `l_shipmode` text column (offsets and bytes), `ok(sv)[j]` the `o_orderkey` of orders row `j` and `oprio(sv)` the
//! `o_orderpriority` text column. For a database `db` bound to the parts (`bound_db`), the projections of the two
//! tables onto the columns the statement reads are `pl_rows(sv)` and `po_rows(sv)` (`lemma_tables`), and the declared
//! primary key makes `o_orderkey` duplicate-free (`lemma_okey_unique`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::typing::*;
use crate::spec::types::*;
use crate::spec::constraints::*;
use crate::gendb_entry::stores::{StoresView, stored_ok};
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::gendb_constraints::declared_db;
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::link::query::{text_at, text_wf, TextView, proj_all, proj};
use crate::link::source::lemma_proj_all_index;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_lineitem::declaration as lid;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_orders::declaration as oid;

verus! {

// ------------------------------------------------------------------------------------------------ column views

/// `l_orderkey` of every lineitem row.
pub open spec fn lok(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_ORDERKEY as int]) }

/// `l_shipdate` of every lineitem row (days since 1970-01-01).
pub open spec fn lsd(sv: StoresView) -> Seq<i32> { li::i32s(sv.flat_lineitem[li::L_SHIPDATE as int]) }

/// `l_commitdate` of every lineitem row (days since 1970-01-01).
pub open spec fn lcd(sv: StoresView) -> Seq<i32> { li::i32s(sv.flat_lineitem[li::L_COMMITDATE as int]) }

/// `l_receiptdate` of every lineitem row (days since 1970-01-01).
pub open spec fn lrd(sv: StoresView) -> Seq<i32> { li::i32s(sv.flat_lineitem[li::L_RECEIPTDATE as int]) }

/// The `l_shipmode` text column (offsets and bytes parts).
pub open spec fn lmode(sv: StoresView) -> TextView {
    li::text_view(sv.flat_lineitem, li::L_SHIPMODE_OFFSETS as int, li::L_SHIPMODE_BYTES as int)
}

/// `o_orderkey` of every orders row.
pub open spec fn ok(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_ORDERKEY as int]) }

/// The `o_orderpriority` text column (offsets and bytes parts).
pub open spec fn oprio(sv: StoresView) -> TextView {
    oi::text_view(sv.flat_orders, oi::O_ORDERPRIORITY_OFFSETS as int, oi::O_ORDERPRIORITY_BYTES as int)
}

/// `l_shipmode` of lineitem row `i` (its bytes).
pub open spec fn mode_at(sv: StoresView, i: int) -> Seq<u8> { text_at(lmode(sv), i) }

/// `o_orderpriority` of orders row `j` (its bytes).
pub open spec fn prio_at(sv: StoresView, j: int) -> Seq<u8> { text_at(oprio(sv), j) }

/// Row counts of the two tables.
pub open spec fn n_l(sv: StoresView) -> int { lok(sv).len() as int }
pub open spec fn n_o(sv: StoresView) -> int { ok(sv).len() as int }

/// The parts have the shape of the two flat storages: every column the query reads has one value per row, and the
/// text columns are well formed. (A consequence of `bound_db`, `lemma_parts_shape`.)
pub open spec fn parts_shape(sv: StoresView) -> bool {
    &&& li::parts_wf(sv.flat_lineitem, n_l(sv))
    &&& oi::parts_wf(sv.flat_orders, n_o(sv))
}

/// The facts about the parts the scan relies on: the column lengths and the well-formed text columns.
pub open spec fn cols_shape(sv: StoresView) -> bool {
    &&& lsd(sv).len() == n_l(sv) && lcd(sv).len() == n_l(sv) && lrd(sv).len() == n_l(sv)
    &&& text_wf(lmode(sv), n_l(sv))
    &&& text_wf(oprio(sv), n_o(sv))
}

/// The values of a key column are pairwise distinct.
pub open spec fn keys_unique(s: Seq<i64>) -> bool {
    forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && #[trigger] s[a] == #[trigger] s[b] ==> a == b
}

// ------------------------------------------------------------------------------------------------ projected rows

/// Table columns of `orders` the statement reads: `o_orderkey`, `o_orderpriority`.
pub open spec fn o_cols() -> Seq<nat> { seq![0nat, 5] }

/// Table columns of `lineitem` the statement reads: `l_orderkey`, `l_shipdate`, `l_commitdate`, `l_receiptdate`,
/// `l_shipmode`.
pub open spec fn l_cols() -> Seq<nat> { seq![0nat, 10, 11, 12, 14] }

/// Orders row `j` projected onto `o_cols()`.
pub open spec fn po_row(sv: StoresView, j: int) -> Row {
    seq![Val::Int(ok(sv)[j] as int), Val::Text(prio_at(sv, j))]
}

/// Lineitem row `i` projected onto `l_cols()`.
pub open spec fn pl_row(sv: StoresView, i: int) -> Row {
    seq![Val::Int(lok(sv)[i] as int), date32_val(lsd(sv)[i]), date32_val(lcd(sv)[i]), date32_val(lrd(sv)[i]),
        Val::Text(mode_at(sv, i))]
}

pub open spec fn po_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_o(sv) as nat, |j: int| po_row(sv, j)) }

pub open spec fn pl_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_l(sv) as nat, |i: int| pl_row(sv, i)) }

// ------------------------------------------------------------------------------------------------ table facts

/// The parts of a bound database have the storages' shape, and the tables have the parts' row counts.
pub proof fn lemma_parts_shape(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        parts_shape(sv),
        cols_shape(sv),
        db.tables.len() == 8,
        db.tables[0].len() == n_l(sv),
        db.tables[1].len() == n_o(sv),
{
    lid::lemma_declared_schema();
    oid::lemma_declared_schema();
    lemma_proj_all_index(db.tables[0], lid::stored_cols_t0());
    lemma_proj_all_index(db.tables[1], oid::stored_cols_t0());
    assert(lid::stored_relations(db)[0].len() == db.tables[0].len());
    assert(oid::stored_relations(db)[0].len() == db.tables[1].len());
}

/// Lineitem row `i`: arity and the five columns the statement reads.
pub proof fn lemma_lineitem_row(sv: StoresView, db: Database, i: int)
    requires bound_db(sv, db), 0 <= i < n_l(sv),
    ensures
        db.tables[0][i].len() == 16,
        db.tables[0][i][0] == Val::Int(lok(sv)[i] as int),
        db.tables[0][i][10] == date32_val(lsd(sv)[i]),
        db.tables[0][i][11] == date32_val(lcd(sv)[i]),
        db.tables[0][i][12] == date32_val(lrd(sv)[i]),
        db.tables[0][i][14] == Val::Text(mode_at(sv, i)),
{
    lemma_parts_shape(sv, db);
    lid::lemma_declared_schema();
    let t = db.tables[0];
    let cols = lid::stored_cols_t0();
    let rels = lid::stored_relations(db);
    lemma_proj_all_index(t, cols);
    assert(rels[0][i] == li::row_at(sv.flat_lineitem, i));
    assert(rels[0][i] == proj(t[i], cols));
    assert(row_in_table(t[i], db.schema[0]));
    assert(cols[0] == 0 && cols[10] == 10 && cols[11] == 11 && cols[12] == 12 && cols[14] == 14);
    assert(proj(t[i], cols)[0] == t[i][0]);
    assert(proj(t[i], cols)[10] == t[i][10]);
    assert(proj(t[i], cols)[11] == t[i][11]);
    assert(proj(t[i], cols)[12] == t[i][12]);
    assert(proj(t[i], cols)[14] == t[i][14]);
}

/// Orders row `j`: arity, `o_orderkey`, `o_orderpriority`.
pub proof fn lemma_orders_row(sv: StoresView, db: Database, j: int)
    requires bound_db(sv, db), 0 <= j < n_o(sv),
    ensures
        db.tables[1][j].len() == 9,
        db.tables[1][j][0] == Val::Int(ok(sv)[j] as int),
        db.tables[1][j][5] == Val::Text(prio_at(sv, j)),
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
    assert(cols[0] == 0 && cols[5] == 5);
    assert(proj(t[j], cols)[0] == t[j][0]);
    assert(proj(t[j], cols)[5] == t[j][5]);
}

/// The projections of the two tables of a bound database are the stored column views, and every table row has
/// its declared arity.
pub proof fn lemma_tables(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        db.tables.len() == 8,
        db.tables[0].len() == n_l(sv),
        db.tables[1].len() == n_o(sv),
        forall|i: int| 0 <= i < n_l(sv) ==> (#[trigger] db.tables[0][i]).len() == 16,
        forall|j: int| 0 <= j < n_o(sv) ==> (#[trigger] db.tables[1][j]).len() == 9,
        proj_all(db.tables[0], l_cols()) == pl_rows(sv),
        proj_all(db.tables[1], o_cols()) == po_rows(sv),
{
    lemma_parts_shape(sv, db);
    let t0 = db.tables[0];
    let t1 = db.tables[1];
    lemma_proj_all_index(t0, l_cols());
    lemma_proj_all_index(t1, o_cols());
    assert forall|i: int| 0 <= i < n_l(sv) implies (#[trigger] t0[i]).len() == 16
        && proj(t0[i], l_cols()) == pl_row(sv, i) by {
        lemma_lineitem_row(sv, db, i);
        assert(proj(t0[i], l_cols()) =~= pl_row(sv, i));
    }
    assert forall|j: int| 0 <= j < n_o(sv) implies (#[trigger] t1[j]).len() == 9
        && proj(t1[j], o_cols()) == po_row(sv, j) by {
        lemma_orders_row(sv, db, j);
        assert(proj(t1[j], o_cols()) =~= po_row(sv, j));
    }
    assert(proj_all(t0, l_cols()) =~= pl_rows(sv));
    assert(proj_all(t1, o_cols()) =~= po_rows(sv));
}

// ------------------------------------------------------------------------------------------------ primary key

/// PRIMARY KEY (o_orderkey): the stored key column of a bound database is duplicate-free.
pub proof fn lemma_okey_unique(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures keys_unique(ok(sv)),
{
    lemma_parts_shape(sv, db);
    crate::gendb_constraints::lemma_declared_schema();
    let ddb = declared_db(db);
    let pk = Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true };
    assert(ddb.schema[1].constraints[0] == pk);
    assert forall|a: int, b: int| 0 <= a < ok(sv).len() && 0 <= b < ok(sv).len() && #[trigger] ok(sv)[a] == #[trigger] ok(sv)[b]
        implies a == b by {
        lemma_orders_row(sv, db, a);
        lemma_orders_row(sv, db, b);
        let kcols = seq![0nat];
        let ka = key_of(db.tables[1][a], kcols);
        let kb = key_of(db.tables[1][b], kcols);
        assert(ka[0] == db.tables[1][a][0]);
        assert(kb[0] == db.tables[1][b][0]);
        assert(crate::spec::equality::val_not_distinct(ka[0], kb[0]));
        assert(crate::spec::equality::row_not_distinct(ka, kb));
        lemma_primary_key_identifies(ddb, 1, 0, kcols, true, a, b);
    }
}

} // verus!
