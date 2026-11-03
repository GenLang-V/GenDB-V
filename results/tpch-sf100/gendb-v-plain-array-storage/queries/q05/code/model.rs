//! The six tables Q5 reads, as functions of the stored parts (`StoresView`): table `t` of every database bound
//! to the parts is exactly `<t>_rows(sv)` (`lemma_tables`), so all later reasoning is about the stored arrays.
//! The declared primary keys give key uniqueness of each table as facts about those arrays (`lemma_keys`), and the
//! declared column types bound the two numeric(15,2) columns the revenue reads (`lemma_vals`).
//!
//! Table ids (schema order): 0 lineitem, 1 orders, 2 customer, 5 supplier, 6 nation, 7 region.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::constraints::*;
use crate::spec::equality::*;
use crate::spec::numeric::{pow10, abs};
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::{proj, proj_all, text_at};
use crate::link::source::lemma_proj_all_index;
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::bridge::equality::lemma_row_not_distinct_refl;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_region::interface as ri;
use crate::stores::flat_lineitem::declaration as ld;
use crate::stores::flat_orders::declaration as od;
use crate::stores::flat_customer::declaration as cd;
use crate::stores::flat_supplier::declaration as sd;
use crate::stores::flat_nation::declaration as nd;
use crate::stores::flat_region::declaration as rd;

verus! {

// ------------------------------------------------------------------------------------------ stored columns

/// Row counts.
pub open spec fn nl(sv: StoresView) -> nat { li::i64s(sv.flat_lineitem[li::L_ORDERKEY as int]).len() }
pub open spec fn no(sv: StoresView) -> nat { oi::i64s(sv.flat_orders[oi::O_ORDERKEY as int]).len() }
pub open spec fn nc(sv: StoresView) -> nat { ci::i64s(sv.flat_customer[ci::C_CUSTKEY as int]).len() }
pub open spec fn ns(sv: StoresView) -> nat { si::i64s(sv.flat_supplier[si::S_SUPPKEY as int]).len() }
pub open spec fn nn(sv: StoresView) -> nat { ni::i64s(sv.flat_nation[ni::N_NATIONKEY as int]).len() }
pub open spec fn nr(sv: StoresView) -> nat { ri::i64s(sv.flat_region[ri::R_REGIONKEY as int]).len() }

/// `lineitem` columns: order key, line number, supplier key, extended price and discount (coefficients, scale 2).
pub open spec fn l_ok(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_ORDERKEY as int]) }
pub open spec fn l_ln(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_LINENUMBER as int]) }
pub open spec fn l_sk(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_SUPPKEY as int]) }
pub open spec fn l_ext(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_EXTENDEDPRICE as int]) }
pub open spec fn l_disc(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_DISCOUNT as int]) }

/// `orders` columns: order key, customer key, order date (days since 1970-01-01).
pub open spec fn o_ok(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_ORDERKEY as int]) }
pub open spec fn o_ck(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_CUSTKEY as int]) }
pub open spec fn o_date(sv: StoresView) -> Seq<i32> { oi::i32s(sv.flat_orders[oi::O_ORDERDATE as int]) }

/// `customer`, `supplier`, `nation`, `region` key columns.
pub open spec fn c_ck(sv: StoresView) -> Seq<i64> { ci::i64s(sv.flat_customer[ci::C_CUSTKEY as int]) }
pub open spec fn c_nk(sv: StoresView) -> Seq<i64> { ci::i64s(sv.flat_customer[ci::C_NATIONKEY as int]) }
pub open spec fn s_sk(sv: StoresView) -> Seq<i64> { si::i64s(sv.flat_supplier[si::S_SUPPKEY as int]) }
pub open spec fn s_nk(sv: StoresView) -> Seq<i64> { si::i64s(sv.flat_supplier[si::S_NATIONKEY as int]) }
pub open spec fn n_nk(sv: StoresView) -> Seq<i64> { ni::i64s(sv.flat_nation[ni::N_NATIONKEY as int]) }
pub open spec fn n_rk(sv: StoresView) -> Seq<i64> { ni::i64s(sv.flat_nation[ni::N_REGIONKEY as int]) }
pub open spec fn r_rk(sv: StoresView) -> Seq<i64> { ri::i64s(sv.flat_region[ri::R_REGIONKEY as int]) }

/// Text columns `n_name` and `r_name`.
pub open spec fn n_name_view(sv: StoresView) -> crate::link::query::TextView {
    ni::text_view(sv.flat_nation, ni::N_NAME_OFFSETS as int, ni::N_NAME_BYTES as int)
}
pub open spec fn r_name_view(sv: StoresView) -> crate::link::query::TextView {
    ri::text_view(sv.flat_region, ri::R_NAME_OFFSETS as int, ri::R_NAME_BYTES as int)
}
pub open spec fn n_name(sv: StoresView, e: int) -> Seq<u8> { text_at(n_name_view(sv), e) }
pub open spec fn r_name(sv: StoresView, f: int) -> Seq<u8> { text_at(r_name_view(sv), f) }

/// The tables as rows of the stored parts.
pub open spec fn l_rows(sv: StoresView) -> Seq<Row> { Seq::new(nl(sv), |i: int| li::row_at(sv.flat_lineitem, i)) }
pub open spec fn o_rows(sv: StoresView) -> Seq<Row> { Seq::new(no(sv), |i: int| oi::row_at(sv.flat_orders, i)) }
pub open spec fn c_rows(sv: StoresView) -> Seq<Row> { Seq::new(nc(sv), |i: int| ci::row_at(sv.flat_customer, i)) }
pub open spec fn s_rows(sv: StoresView) -> Seq<Row> { Seq::new(ns(sv), |i: int| si::row_at(sv.flat_supplier, i)) }
pub open spec fn n_rows(sv: StoresView) -> Seq<Row> { Seq::new(nn(sv), |i: int| ni::row_at(sv.flat_nation, i)) }
pub open spec fn r_rows(sv: StoresView) -> Seq<Row> { Seq::new(nr(sv), |i: int| ri::row_at(sv.flat_region, i)) }

/// The stored parts are well formed (each storage's `parts_wf` at its row count).
pub open spec fn stores_wf(sv: StoresView) -> bool {
    &&& li::parts_wf(sv.flat_lineitem, nl(sv) as int)
    &&& oi::parts_wf(sv.flat_orders, no(sv) as int)
    &&& ci::parts_wf(sv.flat_customer, nc(sv) as int)
    &&& si::parts_wf(sv.flat_supplier, ns(sv) as int)
    &&& ni::parts_wf(sv.flat_nation, nn(sv) as int)
    &&& ri::parts_wf(sv.flat_region, nr(sv) as int)
}

/// The six tables of `db` are the stored ones.
pub open spec fn tables_of(sv: StoresView, db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& db.tables[0] == l_rows(sv)
    &&& db.tables[1] == o_rows(sv)
    &&& db.tables[2] == c_rows(sv)
    &&& db.tables[5] == s_rows(sv)
    &&& db.tables[6] == n_rows(sv)
    &&& db.tables[7] == r_rows(sv)
}

/// No two positions hold the same key.
pub open spec fn keys_unique(keys: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i < keys.len() && 0 <= j < keys.len() && i != j ==> #[trigger] keys[i] != #[trigger] keys[j]
}

/// The declared primary keys, as facts about the stored key columns.
pub open spec fn keys_ok(sv: StoresView) -> bool {
    &&& keys_unique(o_ok(sv))
    &&& keys_unique(c_ck(sv))
    &&& keys_unique(s_sk(sv))
    &&& keys_unique(n_nk(sv))
    &&& keys_unique(r_rk(sv))
    &&& forall|i: int, j: int| 0 <= i < nl(sv) && 0 <= j < nl(sv) && i != j
        ==> #[trigger] l_ok(sv)[i] != #[trigger] l_ok(sv)[j] || l_ln(sv)[i] != l_ln(sv)[j]
}

/// Exclusive bound of the absolute coefficient of a numeric(15,2) value: `10^15`.
pub open spec fn coeff_bound() -> int {
    1_000_000_000_000_000
}

/// The extended price and discount coefficients are numeric(15,2) values.
pub open spec fn vals_ok(sv: StoresView) -> bool {
    forall|c: int| 0 <= c < nl(sv) ==> abs(#[trigger] l_ext(sv)[c] as int) < coeff_bound() && abs(l_disc(sv)[c] as int) < coeff_bound()
}

// ------------------------------------------------------------------------------------------ tables of a bound db

/// Projecting a row on all of its positions in order keeps it.
proof fn lemma_proj_identity(r: Row, cols: Seq<nat>)
    requires r.len() == cols.len(), forall|k: int| 0 <= k < cols.len() ==> #[trigger] cols[k] == k,
    ensures proj(r, cols) == r,
{
    assert(proj(r, cols) =~= r);
}

/// A table of a well-formed database stored with all of its columns (`cols` = 0, 1, ..) is the stored relation.
proof fn lemma_table_is_stored(db: Database, t: int, cols: Seq<nat>, rel: Seq<Row>)
    requires
        db.schema == schema_spec(),
        db_wf(db),
        0 <= t < db.tables.len(),
        db.schema[t].columns.len() == cols.len(),
        forall|k: int| 0 <= k < cols.len() ==> #[trigger] cols[k] == k,
        rel == proj_all(db.tables[t], cols),
    ensures rel == db.tables[t],
{
    let rows = db.tables[t];
    lemma_proj_all_index(rows, cols);
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] rel[i] == rows[i] by {
        assert(row_in_table(rows[i], db.schema[t]));
        lemma_proj_identity(rows[i], cols);
    }
    assert(rel =~= rows);
}

proof fn lemma_l_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[0] == l_rows(sv), li::parts_wf(sv.flat_lineitem, nl(sv) as int), db.tables.len() == 8,
{
    let rels = ld::stored_relations(db);
    ld::lemma_declared_schema();
    let cols = ld::stored_cols_t0();
    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {}
        else if k == 6 {} else if k == 7 {} else if k == 8 {} else if k == 9 {} else if k == 10 {} else if k == 11 {}
        else if k == 12 {} else if k == 13 {} else if k == 14 {} else {}
    }
    lemma_table_is_stored(db, 0, cols, rels[0]);
    let t = db.tables[0];
    assert(li::represents(sv.flat_lineitem, rels));
    assert(t =~= l_rows(sv)) by {
        assert forall|a: int| 0 <= a < t.len() implies #[trigger] t[a] == li::row_at(sv.flat_lineitem, a) by {
            assert(rels[0][a] == li::row_at(sv.flat_lineitem, a));
        }
    }
}

proof fn lemma_o_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[1] == o_rows(sv), oi::parts_wf(sv.flat_orders, no(sv) as int),
{
    let rels = od::stored_relations(db);
    od::lemma_declared_schema();
    let cols = od::stored_cols_t0();
    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {}
        else if k == 6 {} else if k == 7 {} else {}
    }
    lemma_table_is_stored(db, 1, cols, rels[0]);
    let t = db.tables[1];
    assert(oi::represents(sv.flat_orders, rels));
    assert(t =~= o_rows(sv)) by {
        assert forall|a: int| 0 <= a < t.len() implies #[trigger] t[a] == oi::row_at(sv.flat_orders, a) by {
            assert(rels[0][a] == oi::row_at(sv.flat_orders, a));
        }
    }
}

proof fn lemma_c_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[2] == c_rows(sv), ci::parts_wf(sv.flat_customer, nc(sv) as int),
{
    let rels = cd::stored_relations(db);
    cd::lemma_declared_schema();
    let cols = cd::stored_cols_t0();
    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {}
        else if k == 6 {} else {}
    }
    lemma_table_is_stored(db, 2, cols, rels[0]);
    let t = db.tables[2];
    assert(ci::represents(sv.flat_customer, rels));
    assert(t =~= c_rows(sv)) by {
        assert forall|a: int| 0 <= a < t.len() implies #[trigger] t[a] == ci::row_at(sv.flat_customer, a) by {
            assert(rels[0][a] == ci::row_at(sv.flat_customer, a));
        }
    }
}

proof fn lemma_s_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[5] == s_rows(sv), si::parts_wf(sv.flat_supplier, ns(sv) as int),
{
    let rels = sd::stored_relations(db);
    sd::lemma_declared_schema();
    let cols = sd::stored_cols_t0();
    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {} else {}
    }
    lemma_table_is_stored(db, 5, cols, rels[0]);
    let t = db.tables[5];
    assert(si::represents(sv.flat_supplier, rels));
    assert(t =~= s_rows(sv)) by {
        assert forall|a: int| 0 <= a < t.len() implies #[trigger] t[a] == si::row_at(sv.flat_supplier, a) by {
            assert(rels[0][a] == si::row_at(sv.flat_supplier, a));
        }
    }
}

proof fn lemma_n_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[6] == n_rows(sv), ni::parts_wf(sv.flat_nation, nn(sv) as int),
{
    let rels = nd::stored_relations(db);
    nd::lemma_declared_schema();
    let cols = nd::stored_cols_t0();
    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else {}
    }
    lemma_table_is_stored(db, 6, cols, rels[0]);
    let t = db.tables[6];
    assert(ni::represents(sv.flat_nation, rels));
    assert(t =~= n_rows(sv)) by {
        assert forall|a: int| 0 <= a < t.len() implies #[trigger] t[a] == ni::row_at(sv.flat_nation, a) by {
            assert(rels[0][a] == ni::row_at(sv.flat_nation, a));
        }
    }
}

proof fn lemma_r_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[7] == r_rows(sv), ri::parts_wf(sv.flat_region, nr(sv) as int),
{
    let rels = rd::stored_relations(db);
    rd::lemma_declared_schema();
    let cols = rd::stored_cols_t0();
    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else {}
    }
    lemma_table_is_stored(db, 7, cols, rels[0]);
    let t = db.tables[7];
    assert(ri::represents(sv.flat_region, rels));
    assert(t =~= r_rows(sv)) by {
        assert forall|a: int| 0 <= a < t.len() implies #[trigger] t[a] == ri::row_at(sv.flat_region, a) by {
            assert(rels[0][a] == ri::row_at(sv.flat_region, a));
        }
    }
}

/// Every database bound to the parts has the stored tables, and the parts are well formed.
pub proof fn lemma_tables(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures tables_of(sv, db), stores_wf(sv),
{
    lemma_l_table(sv, db);
    lemma_o_table(sv, db);
    lemma_c_table(sv, db);
    lemma_s_table(sv, db);
    lemma_n_table(sv, db);
    lemma_r_table(sv, db);
}

// ------------------------------------------------------------------------------------------ primary keys

/// A single-column primary key of table `t` makes its stored key column duplicate-free.
proof fn lemma_single_key(db: Database, t: int, keys: Seq<i64>)
    requires
        constraints_hold(declared_db(db)),
        db.tables.len() == 8,
        0 <= t < 8,
        declared_schema()[t].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }),
        keys.len() == db.tables[t].len(),
        forall|i: int| 0 <= i < keys.len() ==> #[trigger] db.tables[t][i].len() > 0 && db.tables[t][i][0] == Val::Int(keys[i] as int),
    ensures keys_unique(keys),
{
    let ddb = declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    assert forall|i: int, j: int| 0 <= i < keys.len() && 0 <= j < keys.len() && i != j implies #[trigger] keys[i] != #[trigger] keys[j] by {
        if keys[i] == keys[j] {
            let cols = seq![0nat];
            assert(ddb.tables == db.tables);
            assert(db.tables[t][i].len() > 0 && db.tables[t][i][0] == Val::Int(keys[i] as int));
            assert(db.tables[t][j].len() > 0 && db.tables[t][j][0] == Val::Int(keys[j] as int));
            let ki = key_of(ddb.tables[t][i], cols);
            let kj = key_of(ddb.tables[t][j], cols);
            assert(ki =~= seq![Val::Int(keys[i] as int)]);
            assert(kj =~= seq![Val::Int(keys[j] as int)]);
            lemma_row_not_distinct_refl(ki);
            lemma_primary_key_identifies(ddb, t, 0, cols, true, i, j);
        }
    }
}

/// The primary keys of the six tables hold on the stored key columns.
pub proof fn lemma_keys(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures keys_ok(sv),
{
    lemma_tables(sv, db);
    crate::gendb_constraints::lemma_declared_schema();
    assert(declared_schema()[1].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[2].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[5].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[6].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[7].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[0].constraints[0] == (Constraint::Key { cols: seq![0nat, 3nat], primary: true, nulls_distinct: true }));
    lemma_single_key(db, 1, o_ok(sv));
    lemma_single_key(db, 2, c_ck(sv));
    lemma_single_key(db, 5, s_sk(sv));
    lemma_single_key(db, 6, n_nk(sv));
    lemma_single_key(db, 7, r_rk(sv));
    let ddb = declared_db(db);
    assert forall|i: int, j: int| 0 <= i < nl(sv) && 0 <= j < nl(sv) && i != j
        implies #[trigger] l_ok(sv)[i] != #[trigger] l_ok(sv)[j] || l_ln(sv)[i] != l_ln(sv)[j] by {
        if l_ok(sv)[i] == l_ok(sv)[j] && l_ln(sv)[i] == l_ln(sv)[j] {
            let cols = seq![0nat, 3nat];
            assert(db.tables[0][i] == li::row_at(sv.flat_lineitem, i));
            assert(db.tables[0][j] == li::row_at(sv.flat_lineitem, j));
            let k1 = key_of(ddb.tables[0][i], cols);
            let k2 = key_of(ddb.tables[0][j], cols);
            assert(k1 =~= k2);
            lemma_row_not_distinct_refl(k1);
            lemma_primary_key_identifies(ddb, 0, 0, cols, true, i, j);
        }
    }
}

// ------------------------------------------------------------------------------------------ value bounds

/// The values of a stored `lineitem` row that Q5 reads.
pub proof fn lemma_l_row(sv: StoresView, c: int)
    ensures
        li::row_at(sv.flat_lineitem, c).len() == 16,
        li::row_at(sv.flat_lineitem, c)[0] == Val::Int(l_ok(sv)[c] as int),
        li::row_at(sv.flat_lineitem, c)[2] == Val::Int(l_sk(sv)[c] as int),
        li::row_at(sv.flat_lineitem, c)[3] == Val::Int(l_ln(sv)[c] as int),
        li::row_at(sv.flat_lineitem, c)[5] == (Val::Num { coeff: l_ext(sv)[c] as int, scale: 2 }),
        li::row_at(sv.flat_lineitem, c)[6] == (Val::Num { coeff: l_disc(sv)[c] as int, scale: 2 }),
{
}

/// One row's numeric(15,2) coefficients from the row's declared column domains.
proof fn lemma_val_row(sv: StoresView, db: Database, c: int)
    requires
        db.schema == schema_spec(),
        db_wf(db),
        tables_of(sv, db),
        0 <= c < nl(sv),
        schema_spec()[0].columns[5] == (Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }),
        schema_spec()[0].columns[6] == (Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }),
        pow10(15) == coeff_bound(),
    ensures abs(l_ext(sv)[c] as int) < coeff_bound() && abs(l_disc(sv)[c] as int) < coeff_bound(),
{
    hide(li::row_at);
    hide(value_in_column);
    lemma_l_row(sv, c);
    let r = db.tables[0][c];
    assert(r == li::row_at(sv.flat_lineitem, c));
    assert(row_in_table(r, db.schema[0]));
    assert(value_in_column(r[5], db.schema[0].columns[5]));
    assert(value_in_column(r[6], db.schema[0].columns[6]));
    reveal(value_in_column);
}

/// The declared extended-price and discount coefficients of a bound database are below `10^15` in absolute value.
pub proof fn lemma_vals(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures vals_ok(sv),
{
    lemma_tables(sv, db);
    assert(schema_spec()[0].columns[5] == Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }) by (compute);
    assert(schema_spec()[0].columns[6] == Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }) by (compute);
    assert(pow10(15) == coeff_bound()) by (compute);
    assert forall|c: int| 0 <= c < nl(sv) implies abs(#[trigger] l_ext(sv)[c] as int) < coeff_bound() && abs(l_disc(sv)[c] as int) < coeff_bound() by {
        lemma_val_row(sv, db, c);
    }
}

} // verus!
