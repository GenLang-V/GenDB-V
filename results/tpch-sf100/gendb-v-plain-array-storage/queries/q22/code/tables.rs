//! The two tables the query reads, as functions of the stored parts (`StoresView`): table `t` of every database
//! bound to the parts is exactly `<t>_rows(sv)` (`lemma_model`), so all later reasoning is about the stored arrays.
//! The declared `numeric(15,2)` type bounds the account balance coefficients (`domains_ok`).
//!
//! Table ids (schema order): 1 orders (9 columns, `o_custkey` at 1), 2 customer (8 columns: `c_custkey` at 0,
//! `c_phone` at 4, `c_acctbal` at 5). Balances are coefficients at scale 2 (cents).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::numeric::*;
use crate::schema::schema_spec;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::{proj, proj_all, text_at, TextView};
use crate::link::source::lemma_proj_all_index;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_orders::declaration as od;
use crate::stores::flat_customer::declaration as cd;

verus! {

// ------------------------------------------------------------------------------------------ stored columns

/// Row counts.
pub open spec fn n_o(sv: StoresView) -> nat { oi::i64s(sv.flat_orders[oi::O_CUSTKEY as int]).len() }
pub open spec fn n_c(sv: StoresView) -> nat { ci::i64s(sv.flat_customer[ci::C_CUSTKEY as int]).len() }

/// `o_custkey` of every orders row; `c_custkey` and `c_acctbal` (coefficients at scale 2) of every customer row.
pub open spec fn ock(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_CUSTKEY as int]) }
pub open spec fn cck(sv: StoresView) -> Seq<i64> { ci::i64s(sv.flat_customer[ci::C_CUSTKEY as int]) }
pub open spec fn bal(sv: StoresView) -> Seq<i128> { ci::i128s(sv.flat_customer[ci::C_ACCTBAL as int]) }

/// The `c_phone` text column, and the phone of customer row `i`.
pub open spec fn phone_col(sv: StoresView) -> TextView {
    ci::text_view(sv.flat_customer, ci::C_PHONE_OFFSETS as int, ci::C_PHONE_BYTES as int)
}
pub open spec fn phone(sv: StoresView, i: int) -> Seq<u8> { text_at(phone_col(sv), i) }

/// The tables as rows of the stored parts.
pub open spec fn orders_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_o(sv), |j: int| oi::row_at(sv.flat_orders, j)) }
pub open spec fn cust_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_c(sv), |i: int| ci::row_at(sv.flat_customer, i)) }

/// The stored parts are well formed (each storage's `parts_wf` at its row count).
pub open spec fn stores_wf(sv: StoresView) -> bool {
    &&& oi::parts_wf(sv.flat_orders, n_o(sv) as int)
    &&& ci::parts_wf(sv.flat_customer, n_c(sv) as int)
}

/// The two tables of `db` are the stored ones.
pub open spec fn tables_of(sv: StoresView, db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& db.tables[1] == orders_rows(sv)
    &&& db.tables[2] == cust_rows(sv)
}

/// Values of the declared numeric(15,2) column: `|coefficient| < 10^15`.
pub open spec fn num15(c: i128) -> bool { -1_000_000_000_000_000 < c < 1_000_000_000_000_000 }

/// The declared column domain the query relies on: balance coefficients have at most 15 digits.
pub open spec fn domains_ok(sv: StoresView) -> bool {
    forall|i: int| 0 <= i < n_c(sv) ==> num15(#[trigger] bal(sv)[i])
}

/// The customer row count is below `2^61` (the `c_custkey` part is a slice of 8-byte elements inside the address
/// space; the query establishes it from the slice's size).
pub open spec fn sizes_ok(sv: StoresView) -> bool {
    n_c(sv) <= 0x1fff_ffff_ffff_ffff
}

/// Everything about the stored parts that holds for every bound database.
pub open spec fn model_ok(sv: StoresView) -> bool {
    &&& stores_wf(sv)
    &&& domains_ok(sv)
}

// ------------------------------------------------------------------------------------------ row values

/// Orders row `j`: 9 columns, `o_custkey` at 1.
#[verifier::spinoff_prover]
pub proof fn lemma_orders_row(sv: StoresView, j: int)
    requires 0 <= j < n_o(sv),
    ensures
        orders_rows(sv)[j].len() == 9,
        orders_rows(sv)[j][1] == Val::Int(ock(sv)[j] as int),
{
}

/// Customer row `i`: 8 columns, `c_custkey` at 0, `c_phone` at 4, `c_acctbal` at 5.
#[verifier::spinoff_prover]
pub proof fn lemma_cust_row(sv: StoresView, i: int)
    requires 0 <= i < n_c(sv),
    ensures
        cust_rows(sv)[i].len() == 8,
        cust_rows(sv)[i][0] == Val::Int(cck(sv)[i] as int),
        cust_rows(sv)[i][4] == Val::Text(phone(sv, i)),
        cust_rows(sv)[i][5] == (Val::Num { coeff: bal(sv)[i] as int, scale: 2 }),
{
}

// ------------------------------------------------------------------------------------------ tables of a bound db

/// Projecting a row on all of its positions in order keeps it.
#[verifier::spinoff_prover]
proof fn lemma_proj_identity(r: Row, cols: Seq<nat>)
    requires r.len() == cols.len(), forall|k: int| 0 <= k < cols.len() ==> #[trigger] cols[k] == k,
    ensures proj(r, cols) == r,
{
    assert(proj(r, cols) =~= r);
}

/// A table of a well-formed database stored with all of its columns (`cols` = 0, 1, ..) is the stored relation.
#[verifier::spinoff_prover]
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

#[verifier::spinoff_prover]
proof fn lemma_orders_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[1] == orders_rows(sv), oi::parts_wf(sv.flat_orders, n_o(sv) as int), db.tables.len() == 8,
{
    let rels = od::stored_relations(db);
    od::lemma_declared_schema();
    od::lemma_stored_relations(db);
    let cols = od::stored_cols_t0();
    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {}
        else if k == 6 {} else if k == 7 {} else {}
    }
    lemma_table_is_stored(db, 1, cols, rels[0]);
    let t = db.tables[1];
    assert(oi::represents(sv.flat_orders, rels));
    assert(oi::i64s(sv.flat_orders[oi::O_CUSTKEY as int]).len() == t.len());
    assert(t =~= orders_rows(sv)) by {
        assert forall|a: int| 0 <= a < t.len() implies #[trigger] t[a] == oi::row_at(sv.flat_orders, a) by {
            assert(rels[0][a] == oi::row_at(sv.flat_orders, a));
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_cust_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[2] == cust_rows(sv), ci::parts_wf(sv.flat_customer, n_c(sv) as int),
{
    let rels = cd::stored_relations(db);
    cd::lemma_declared_schema();
    cd::lemma_stored_relations(db);
    let cols = cd::stored_cols_t0();
    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {}
        else if k == 6 {} else {}
    }
    lemma_table_is_stored(db, 2, cols, rels[0]);
    let t = db.tables[2];
    assert(ci::represents(sv.flat_customer, rels));
    assert(ci::i64s(sv.flat_customer[ci::C_CUSTKEY as int]).len() == t.len());
    assert(t =~= cust_rows(sv)) by {
        assert forall|a: int| 0 <= a < t.len() implies #[trigger] t[a] == ci::row_at(sv.flat_customer, a) by {
            assert(rels[0][a] == ci::row_at(sv.flat_customer, a));
        }
    }
}

/// The declared numeric(15,2) type bounds the stored balance coefficients.
#[verifier::spinoff_prover]
proof fn lemma_domains(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures domains_ok(sv),
{
    lemma_cust_table(sv, db);
    let rels = cd::stored_relations(db);
    cd::lemma_stored_relations(db);
    let cs = cd::stored_columns_t0();
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
    assert forall|i: int| 0 <= i < n_c(sv) implies num15(#[trigger] bal(sv)[i]) by {
        let r = rels[0][i];
        assert(r == ci::row_at(sv.flat_customer, i));
        assert(value_in_column(r[5], cs[5]));
    }
}

/// Every fact of the model, for every bound database.
#[verifier::spinoff_prover]
pub proof fn lemma_model(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures model_ok(sv), tables_of(sv, db),
{
    lemma_orders_table(sv, db);
    lemma_cust_table(sv, db);
    lemma_domains(sv, db);
}

} // verus!
