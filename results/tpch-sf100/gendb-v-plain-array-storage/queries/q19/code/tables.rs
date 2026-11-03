//! The two tables the query reads, as functions of the stored parts (`StoresView`): table `t` of every database
//! bound to the parts is exactly `<t>_rows(sv)` (`lemma_tables`), so all later reasoning is about the stored
//! arrays. The declared primary key of `part` makes its stored key column duplicate-free (`lemma_part_key`), and the
//! declared `numeric(15,2)` types bound the price and discount coefficients (`lemma_domains`).
//!
//! Table ids (schema order): 0 lineitem (16 columns), 3 part (9 columns).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::numeric::*;
use crate::spec::constraints::*;
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::{proj, proj_all, text_at, TextView};
use crate::link::source::lemma_proj_all_index;
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::bridge::equality::lemma_row_not_distinct_refl;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_lineitem::declaration as ld;
use crate::stores::flat_part::declaration as pd;

verus! {

// ------------------------------------------------------------------------------------------ stored columns

/// Row counts.
pub open spec fn n_l(sv: StoresView) -> nat { li::i64s(sv.flat_lineitem[li::L_ORDERKEY as int]).len() }
pub open spec fn n_p(sv: StoresView) -> nat { pi::i64s(sv.flat_part[pi::P_PARTKEY as int]).len() }

/// Lineitem: `l_partkey`; `l_quantity`, `l_extendedprice` and `l_discount` (coefficients, scale 2).
pub open spec fn l_pkey(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_PARTKEY as int]) }
pub open spec fn l_qty(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_QUANTITY as int]) }
pub open spec fn l_price(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_EXTENDEDPRICE as int]) }
pub open spec fn l_disc(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_DISCOUNT as int]) }

/// Lineitem text columns `l_shipinstruct` and `l_shipmode`.
pub open spec fn instr_col(sv: StoresView) -> TextView {
    li::text_view(sv.flat_lineitem, li::L_SHIPINSTRUCT_OFFSETS as int, li::L_SHIPINSTRUCT_BYTES as int)
}
pub open spec fn mode_col(sv: StoresView) -> TextView {
    li::text_view(sv.flat_lineitem, li::L_SHIPMODE_OFFSETS as int, li::L_SHIPMODE_BYTES as int)
}
pub open spec fn l_instr(sv: StoresView, l: int) -> Seq<u8> { text_at(instr_col(sv), l) }
pub open spec fn l_mode(sv: StoresView, l: int) -> Seq<u8> { text_at(mode_col(sv), l) }

/// Part: `p_partkey`, `p_size`, and the text columns `p_brand` and `p_container`.
pub open spec fn p_key(sv: StoresView) -> Seq<i64> { pi::i64s(sv.flat_part[pi::P_PARTKEY as int]) }
pub open spec fn p_size(sv: StoresView) -> Seq<i64> { pi::i64s(sv.flat_part[pi::P_SIZE as int]) }
pub open spec fn brand_col(sv: StoresView) -> TextView {
    pi::text_view(sv.flat_part, pi::P_BRAND_OFFSETS as int, pi::P_BRAND_BYTES as int)
}
pub open spec fn cont_col(sv: StoresView) -> TextView {
    pi::text_view(sv.flat_part, pi::P_CONTAINER_OFFSETS as int, pi::P_CONTAINER_BYTES as int)
}
pub open spec fn p_brand(sv: StoresView, a: int) -> Seq<u8> { text_at(brand_col(sv), a) }
pub open spec fn p_cont(sv: StoresView, a: int) -> Seq<u8> { text_at(cont_col(sv), a) }

/// The tables as rows of the stored parts.
pub open spec fn line_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_l(sv), |i: int| li::row_at(sv.flat_lineitem, i)) }
pub open spec fn part_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_p(sv), |i: int| pi::row_at(sv.flat_part, i)) }

/// The stored parts are well formed (each storage's `parts_wf` at its row count).
pub open spec fn stores_wf(sv: StoresView) -> bool {
    &&& li::parts_wf(sv.flat_lineitem, n_l(sv) as int)
    &&& pi::parts_wf(sv.flat_part, n_p(sv) as int)
}

/// The two tables of `db` are the stored ones.
pub open spec fn tables_of(sv: StoresView, db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& db.tables[0] == line_rows(sv)
    &&& db.tables[3] == part_rows(sv)
}

/// The values of a key column are pairwise distinct.
pub open spec fn keys_unique(keys: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i < keys.len() && 0 <= j < keys.len() && i != j ==> keys[i] != keys[j]
}

/// Values of the declared numeric(15,2) columns: `|coefficient| < 10^15`.
pub open spec fn num15(c: i128) -> bool { -1_000_000_000_000_000 < c < 1_000_000_000_000_000 }

/// The declared column domains the query relies on: price and discount coefficients have at most 15 digits.
pub open spec fn domains_ok(sv: StoresView) -> bool {
    forall|i: int| 0 <= i < n_l(sv) ==> num15(#[trigger] l_price(sv)[i]) && num15(l_disc(sv)[i])
}

/// Everything about the stored parts that holds for every bound database.
pub open spec fn model_ok(sv: StoresView) -> bool {
    &&& stores_wf(sv)
    &&& keys_unique(p_key(sv))
    &&& domains_ok(sv)
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

proof fn lemma_line_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        db.tables[0] == line_rows(sv), li::parts_wf(sv.flat_lineitem, n_l(sv) as int), db.tables.len() == 8,
{
    let rels = ld::stored_relations(db);
    ld::lemma_declared_schema();
    ld::lemma_stored_relations(db);
    let cols = ld::stored_cols_t0();
    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {}
        else if k == 6 {} else if k == 7 {} else if k == 8 {} else if k == 9 {} else if k == 10 {} else if k == 11 {}
        else if k == 12 {} else if k == 13 {} else if k == 14 {} else {}
    }
    lemma_table_is_stored(db, 0, cols, rels[0]);
    let t = db.tables[0];
    assert(li::represents(sv.flat_lineitem, rels));
    assert(t =~= line_rows(sv)) by {
        assert forall|a: int| 0 <= a < t.len() implies #[trigger] t[a] == li::row_at(sv.flat_lineitem, a) by {
            assert(rels[0][a] == li::row_at(sv.flat_lineitem, a));
        }
    }
}

proof fn lemma_part_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[3] == part_rows(sv), pi::parts_wf(sv.flat_part, n_p(sv) as int),
{
    let rels = pd::stored_relations(db);
    pd::lemma_declared_schema();
    ld::lemma_declared_schema();
    let cols = pd::stored_cols_t0();
    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {}
        else if k == 6 {} else if k == 7 {} else {}
    }
    lemma_table_is_stored(db, 3, cols, rels[0]);
    let t = db.tables[3];
    assert(pi::represents(sv.flat_part, rels));
    assert(t =~= part_rows(sv)) by {
        assert forall|a: int| 0 <= a < t.len() implies #[trigger] t[a] == pi::row_at(sv.flat_part, a) by {
            assert(rels[0][a] == pi::row_at(sv.flat_part, a));
        }
    }
}

/// Every database bound to the parts has the stored tables, and the parts are well formed.
pub proof fn lemma_tables(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures tables_of(sv, db), stores_wf(sv),
{
    lemma_line_table(sv, db);
    lemma_part_table(sv, db);
}

// ------------------------------------------------------------------------------------------ primary key of part

/// PRIMARY KEY (p_partkey): the stored part key column is duplicate-free.
proof fn lemma_part_key(sv: StoresView, db: Database)
    requires bound_db(sv, db), tables_of(sv, db),
    ensures keys_unique(p_key(sv)),
{
    let ddb = declared_db(db);
    let keys = p_key(sv);
    crate::gendb_constraints::lemma_declared_schema();
    let cols = seq![0nat];
    assert(declared_schema()[3].constraints[0] == (Constraint::Key { cols, primary: true, nulls_distinct: true }));
    assert forall|i: int, j: int| 0 <= i < keys.len() && 0 <= j < keys.len() && i != j implies keys[i] != keys[j] by {
        if keys[i] == keys[j] {
            assert(ddb.tables == db.tables);
            assert(db.tables[3][i] == pi::row_at(sv.flat_part, i));
            assert(db.tables[3][j] == pi::row_at(sv.flat_part, j));
            let ki = key_of(ddb.tables[3][i], cols);
            let kj = key_of(ddb.tables[3][j], cols);
            assert(ki =~= seq![Val::Int(keys[i] as int)]);
            assert(kj =~= seq![Val::Int(keys[j] as int)]);
            lemma_row_not_distinct_refl(ki);
            lemma_primary_key_identifies(ddb, 3, 0, cols, true, i, j);
        }
    }
}

/// The declared numeric(15,2) types bound the stored price and discount coefficients.
proof fn lemma_domains(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures domains_ok(sv),
{
    lemma_line_table(sv, db);
    let rels = ld::stored_relations(db);
    ld::lemma_stored_relations(db);
    let cs = ld::stored_columns_t0();
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
    assert forall|i: int| 0 <= i < n_l(sv) implies num15(#[trigger] l_price(sv)[i]) && num15(l_disc(sv)[i]) by {
        let r = rels[0][i];
        assert(r == li::row_at(sv.flat_lineitem, i));
        assert(value_in_column(r[5], cs[5]));
        assert(value_in_column(r[6], cs[6]));
    }
}

/// Every fact of the model, for every bound database.
pub proof fn lemma_model(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures model_ok(sv), tables_of(sv, db),
{
    lemma_tables(sv, db);
    lemma_part_key(sv, db);
    lemma_domains(sv, db);
}

} // verus!
