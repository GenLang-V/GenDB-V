//! The five tables the query reads, as functions of the stored parts (`StoresView`): table `t` of every database
//! bound to the parts is exactly `<t>_rows(sv)` (`lemma_model`), so all later reasoning is about the stored arrays.
//! The declared `numeric(15,2)` type of `l_quantity` bounds its coefficients (`domains_ok`).
//!
//! Table ids (schema order): 0 lineitem (16 columns), 3 part (9), 4 partsupp (5), 5 supplier (7), 6 nation (4).
//! Quantities are coefficients at scale 2 (hundredths); stored dates are days since 1970-01-01.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::typing::*;
use crate::spec::numeric::*;
use crate::schema::schema_spec;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::{proj, proj_all, text_at, TextView};
use crate::link::source::lemma_proj_all_index;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_partsupp::interface as psi;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_lineitem::declaration as ld;
use crate::stores::flat_part::declaration as pd;
use crate::stores::flat_partsupp::declaration as psd;
use crate::stores::flat_supplier::declaration as sd;
use crate::stores::flat_nation::declaration as nd;
use crate::spec::constraints::*;
use crate::spec::types::Constraint;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::bridge::equality::lemma_row_not_distinct_refl;

verus! {

// ------------------------------------------------------------------------------------------ stored columns

/// Row counts.
pub open spec fn n_l(sv: StoresView) -> nat { li::i64s(sv.flat_lineitem[li::L_ORDERKEY as int]).len() }
pub open spec fn n_p(sv: StoresView) -> nat { pi::i64s(sv.flat_part[pi::P_PARTKEY as int]).len() }
pub open spec fn n_ps(sv: StoresView) -> nat { psi::i64s(sv.flat_partsupp[psi::PS_PARTKEY as int]).len() }
pub open spec fn n_s(sv: StoresView) -> nat { si::i64s(sv.flat_supplier[si::S_SUPPKEY as int]).len() }
pub open spec fn n_n(sv: StoresView) -> nat { ni::i64s(sv.flat_nation[ni::N_NATIONKEY as int]).len() }

/// Lineitem: `l_partkey`, `l_suppkey`, `l_shipdate` (days since 1970-01-01), `l_quantity` (coefficients, scale 2).
pub open spec fn lpk(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_PARTKEY as int]) }
pub open spec fn lsk(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_SUPPKEY as int]) }
pub open spec fn lsd(sv: StoresView) -> Seq<i32> { li::i32s(sv.flat_lineitem[li::L_SHIPDATE as int]) }
pub open spec fn lqt(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_QUANTITY as int]) }

/// Part: `p_partkey` and the `p_name` text column.
pub open spec fn pk(sv: StoresView) -> Seq<i64> { pi::i64s(sv.flat_part[pi::P_PARTKEY as int]) }
pub open spec fn pname_col(sv: StoresView) -> TextView {
    pi::text_view(sv.flat_part, pi::P_NAME_OFFSETS as int, pi::P_NAME_BYTES as int)
}
pub open spec fn pname(sv: StoresView, p: int) -> Seq<u8> { text_at(pname_col(sv), p) }

/// Partsupp: `ps_partkey`, `ps_suppkey`, `ps_availqty`.
pub open spec fn pspk(sv: StoresView) -> Seq<i64> { psi::i64s(sv.flat_partsupp[psi::PS_PARTKEY as int]) }
pub open spec fn pssk(sv: StoresView) -> Seq<i64> { psi::i64s(sv.flat_partsupp[psi::PS_SUPPKEY as int]) }
pub open spec fn psaq(sv: StoresView) -> Seq<i64> { psi::i64s(sv.flat_partsupp[psi::PS_AVAILQTY as int]) }

/// Supplier: `s_suppkey`, `s_nationkey`, and the `s_name`, `s_address` text columns.
pub open spec fn sk(sv: StoresView) -> Seq<i64> { si::i64s(sv.flat_supplier[si::S_SUPPKEY as int]) }
pub open spec fn snk(sv: StoresView) -> Seq<i64> { si::i64s(sv.flat_supplier[si::S_NATIONKEY as int]) }
pub open spec fn sname_col(sv: StoresView) -> TextView {
    si::text_view(sv.flat_supplier, si::S_NAME_OFFSETS as int, si::S_NAME_BYTES as int)
}
pub open spec fn saddr_col(sv: StoresView) -> TextView {
    si::text_view(sv.flat_supplier, si::S_ADDRESS_OFFSETS as int, si::S_ADDRESS_BYTES as int)
}
pub open spec fn sname(sv: StoresView, s: int) -> Seq<u8> { text_at(sname_col(sv), s) }
pub open spec fn saddr(sv: StoresView, s: int) -> Seq<u8> { text_at(saddr_col(sv), s) }

/// Nation: `n_nationkey` and the `n_name` text column.
pub open spec fn nk(sv: StoresView) -> Seq<i64> { ni::i64s(sv.flat_nation[ni::N_NATIONKEY as int]) }
pub open spec fn nname_col(sv: StoresView) -> TextView {
    ni::text_view(sv.flat_nation, ni::N_NAME_OFFSETS as int, ni::N_NAME_BYTES as int)
}
pub open spec fn nname(sv: StoresView, a: int) -> Seq<u8> { text_at(nname_col(sv), a) }

/// The tables as rows of the stored parts.
pub open spec fn line_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_l(sv), |i: int| li::row_at(sv.flat_lineitem, i)) }
pub open spec fn part_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_p(sv), |i: int| pi::row_at(sv.flat_part, i)) }
pub open spec fn ps_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_ps(sv), |i: int| psi::row_at(sv.flat_partsupp, i)) }
pub open spec fn supp_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_s(sv), |i: int| si::row_at(sv.flat_supplier, i)) }
pub open spec fn nat_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_n(sv), |i: int| ni::row_at(sv.flat_nation, i)) }

/// The stored parts are well formed (each storage's `parts_wf` at its row count).
pub open spec fn stores_wf(sv: StoresView) -> bool {
    &&& li::parts_wf(sv.flat_lineitem, n_l(sv) as int)
    &&& pi::parts_wf(sv.flat_part, n_p(sv) as int)
    &&& psi::parts_wf(sv.flat_partsupp, n_ps(sv) as int)
    &&& si::parts_wf(sv.flat_supplier, n_s(sv) as int)
    &&& ni::parts_wf(sv.flat_nation, n_n(sv) as int)
}

/// The tables of `db` the query reads are the stored ones.
pub open spec fn tables_of(sv: StoresView, db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& db.tables[0] == line_rows(sv)
    &&& db.tables[3] == part_rows(sv)
    &&& db.tables[4] == ps_rows(sv)
    &&& db.tables[5] == supp_rows(sv)
    &&& db.tables[6] == nat_rows(sv)
}

/// Values of the declared numeric(15,2) columns: `|coefficient| < 10^15`.
pub open spec fn num15(c: i128) -> bool { -1_000_000_000_000_000 < c < 1_000_000_000_000_000 }

/// The declared column domain the query relies on: quantity coefficients have at most 15 digits.
pub open spec fn domains_ok(sv: StoresView) -> bool {
    forall|i: int| 0 <= i < n_l(sv) ==> num15(#[trigger] lqt(sv)[i])
}

/// The values of a key column are pairwise distinct.
pub open spec fn keys_unique(keys: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i < keys.len() && 0 <= j < keys.len() && i != j ==> keys[i] != keys[j]
}

/// Everything about the stored parts that holds for every bound database.
pub open spec fn model_ok(sv: StoresView) -> bool {
    &&& stores_wf(sv)
    &&& domains_ok(sv)
    &&& keys_unique(nk(sv))
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
    ensures db.tables[0] == line_rows(sv), li::parts_wf(sv.flat_lineitem, n_l(sv) as int), db.tables.len() == 8,
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

proof fn lemma_ps_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[4] == ps_rows(sv), psi::parts_wf(sv.flat_partsupp, n_ps(sv) as int),
{
    let rels = psd::stored_relations(db);
    psd::lemma_declared_schema();
    ld::lemma_declared_schema();
    let cols = psd::stored_cols_t0();
    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else {}
    }
    lemma_table_is_stored(db, 4, cols, rels[0]);
    let t = db.tables[4];
    assert(psi::represents(sv.flat_partsupp, rels));
    assert(t =~= ps_rows(sv)) by {
        assert forall|a: int| 0 <= a < t.len() implies #[trigger] t[a] == psi::row_at(sv.flat_partsupp, a) by {
            assert(rels[0][a] == psi::row_at(sv.flat_partsupp, a));
        }
    }
}

proof fn lemma_supp_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[5] == supp_rows(sv), si::parts_wf(sv.flat_supplier, n_s(sv) as int),
{
    let rels = sd::stored_relations(db);
    sd::lemma_declared_schema();
    ld::lemma_declared_schema();
    let cols = sd::stored_cols_t0();
    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {} else {}
    }
    lemma_table_is_stored(db, 5, cols, rels[0]);
    let t = db.tables[5];
    assert(si::represents(sv.flat_supplier, rels));
    assert(t =~= supp_rows(sv)) by {
        assert forall|a: int| 0 <= a < t.len() implies #[trigger] t[a] == si::row_at(sv.flat_supplier, a) by {
            assert(rels[0][a] == si::row_at(sv.flat_supplier, a));
        }
    }
}

proof fn lemma_nat_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[6] == nat_rows(sv), ni::parts_wf(sv.flat_nation, n_n(sv) as int),
{
    let rels = nd::stored_relations(db);
    nd::lemma_declared_schema();
    ld::lemma_declared_schema();
    let cols = nd::stored_cols_t0();
    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else {}
    }
    lemma_table_is_stored(db, 6, cols, rels[0]);
    let t = db.tables[6];
    assert(ni::represents(sv.flat_nation, rels));
    assert(t =~= nat_rows(sv)) by {
        assert forall|a: int| 0 <= a < t.len() implies #[trigger] t[a] == ni::row_at(sv.flat_nation, a) by {
            assert(rels[0][a] == ni::row_at(sv.flat_nation, a));
        }
    }
}

/// The declared numeric(15,2) type bounds the stored quantity coefficients.
proof fn lemma_domains(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures domains_ok(sv),
{
    lemma_line_table(sv, db);
    let rels = ld::stored_relations(db);
    ld::lemma_stored_relations(db);
    let cs = ld::stored_columns_t0();
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
    assert forall|i: int| 0 <= i < n_l(sv) implies num15(#[trigger] lqt(sv)[i]) by {
        let r = rels[0][i];
        assert(r == li::row_at(sv.flat_lineitem, i));
        assert(value_in_column(r[4], cs[4]));
    }
}

/// PRIMARY KEY (n_nationkey): the stored nation key column is duplicate-free.
proof fn lemma_nation_key(sv: StoresView, db: Database)
    requires bound_db(sv, db), db.tables[6] == nat_rows(sv), db.tables.len() == 8,
    ensures keys_unique(nk(sv)),
{
    let ddb = declared_db(db);
    let keys = nk(sv);
    crate::gendb_constraints::lemma_declared_schema();
    let cols = seq![0nat];
    assert(declared_schema()[6].constraints[0] == (Constraint::Key { cols, primary: true, nulls_distinct: true }));
    assert forall|i: int, j: int| 0 <= i < keys.len() && 0 <= j < keys.len() && i != j implies keys[i] != keys[j] by {
        if keys[i] == keys[j] {
            assert(ddb.tables == db.tables);
            assert(db.tables[6][i] == ni::row_at(sv.flat_nation, i));
            assert(db.tables[6][j] == ni::row_at(sv.flat_nation, j));
            let ki = key_of(ddb.tables[6][i], cols);
            let kj = key_of(ddb.tables[6][j], cols);
            assert(ki =~= seq![Val::Int(keys[i] as int)]);
            assert(kj =~= seq![Val::Int(keys[j] as int)]);
            lemma_row_not_distinct_refl(ki);
            lemma_primary_key_identifies(ddb, 6, 0, cols, true, i, j);
        }
    }
}

/// Every fact of the model, for every bound database.
pub proof fn lemma_model(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures model_ok(sv), tables_of(sv, db),
{
    lemma_line_table(sv, db);
    lemma_part_table(sv, db);
    lemma_ps_table(sv, db);
    lemma_supp_table(sv, db);
    lemma_nat_table(sv, db);
    lemma_domains(sv, db);
    lemma_nation_key(sv, db);
}

} // verus!
