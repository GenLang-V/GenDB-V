//! The seven tables the query reads, as functions of the stored parts (`StoresView`): table `t` of every database
//! bound to the parts is exactly `<t>_rows(sv)` (`lemma_tables`), so all later reasoning is about the stored
//! arrays. The declared primary keys give key uniqueness of each table as facts about those arrays (`lemma_keys`),
//! and the declared column types bound the numeric coefficients (`lemma_domains`).
//!
//! Table ids (schema order): 0 lineitem, 1 orders, 2 customer, 3 part, 5 supplier, 6 nation, 7 region.
//! Stored dates count days since 1970-01-01 (`date32_val(x)` is the SQL date `x - 10957`, days since 2000-01-01).
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
use crate::link::query::{proj, proj_all, text_at};
use crate::link::source::{lemma_proj_all_index, rows_in_columns};
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::bridge::equality::lemma_row_not_distinct_refl;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_region::interface as ri;
use crate::stores::flat_lineitem::declaration as ld;
use crate::stores::flat_orders::declaration as od;
use crate::stores::flat_customer::declaration as cd;
use crate::stores::flat_part::declaration as pd;
use crate::stores::flat_supplier::declaration as sd;
use crate::stores::flat_nation::declaration as nd;
use crate::stores::flat_region::declaration as rd;

verus! {

// ------------------------------------------------------------------------------------------ stored columns

/// Row counts.
pub open spec fn n_l(sv: StoresView) -> nat { li::i64s(sv.flat_lineitem[li::L_ORDERKEY as int]).len() }
pub open spec fn n_o(sv: StoresView) -> nat { oi::i64s(sv.flat_orders[oi::O_ORDERKEY as int]).len() }
pub open spec fn n_c(sv: StoresView) -> nat { ci::i64s(sv.flat_customer[ci::C_CUSTKEY as int]).len() }
pub open spec fn n_p(sv: StoresView) -> nat { pi::i64s(sv.flat_part[pi::P_PARTKEY as int]).len() }
pub open spec fn n_s(sv: StoresView) -> nat { si::i64s(sv.flat_supplier[si::S_SUPPKEY as int]).len() }
pub open spec fn n_n(sv: StoresView) -> nat { ni::i64s(sv.flat_nation[ni::N_NATIONKEY as int]).len() }
pub open spec fn n_r(sv: StoresView) -> nat { ri::i64s(sv.flat_region[ri::R_REGIONKEY as int]).len() }

/// Lineitem: `l_orderkey`, `l_partkey`, `l_suppkey`, `l_extendedprice` and `l_discount` (coefficients, scale 2).
pub open spec fn l_okey(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_ORDERKEY as int]) }
pub open spec fn l_pkey(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_PARTKEY as int]) }
pub open spec fn l_skey(sv: StoresView) -> Seq<i64> { li::i64s(sv.flat_lineitem[li::L_SUPPKEY as int]) }
pub open spec fn l_price(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_EXTENDEDPRICE as int]) }
pub open spec fn l_disc(sv: StoresView) -> Seq<i128> { li::i128s(sv.flat_lineitem[li::L_DISCOUNT as int]) }

/// Orders: `o_orderkey`, `o_custkey`, `o_orderdate` (days since 1970-01-01).
pub open spec fn o_key(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_ORDERKEY as int]) }
pub open spec fn o_cust(sv: StoresView) -> Seq<i64> { oi::i64s(sv.flat_orders[oi::O_CUSTKEY as int]) }
pub open spec fn o_date(sv: StoresView) -> Seq<i32> { oi::i32s(sv.flat_orders[oi::O_ORDERDATE as int]) }

/// Customer: `c_custkey`, `c_nationkey`.
pub open spec fn c_key(sv: StoresView) -> Seq<i64> { ci::i64s(sv.flat_customer[ci::C_CUSTKEY as int]) }
pub open spec fn c_nat(sv: StoresView) -> Seq<i64> { ci::i64s(sv.flat_customer[ci::C_NATIONKEY as int]) }

/// Part: `p_partkey`, `p_type`.
pub open spec fn p_key(sv: StoresView) -> Seq<i64> { pi::i64s(sv.flat_part[pi::P_PARTKEY as int]) }
pub open spec fn p_type(sv: StoresView, a: int) -> Seq<u8> {
    text_at(pi::text_view(sv.flat_part, pi::P_TYPE_OFFSETS as int, pi::P_TYPE_BYTES as int), a)
}

/// Supplier: `s_suppkey`, `s_nationkey`.
pub open spec fn s_key(sv: StoresView) -> Seq<i64> { si::i64s(sv.flat_supplier[si::S_SUPPKEY as int]) }
pub open spec fn s_nat(sv: StoresView) -> Seq<i64> { si::i64s(sv.flat_supplier[si::S_NATIONKEY as int]) }

/// Nation: `n_nationkey`, `n_regionkey`, `n_name`.
pub open spec fn n_key(sv: StoresView) -> Seq<i64> { ni::i64s(sv.flat_nation[ni::N_NATIONKEY as int]) }
pub open spec fn n_reg(sv: StoresView) -> Seq<i64> { ni::i64s(sv.flat_nation[ni::N_REGIONKEY as int]) }
pub open spec fn n_name(sv: StoresView, d: int) -> Seq<u8> {
    text_at(ni::text_view(sv.flat_nation, ni::N_NAME_OFFSETS as int, ni::N_NAME_BYTES as int), d)
}

/// Region: `r_regionkey`, `r_name`.
pub open spec fn r_key(sv: StoresView) -> Seq<i64> { ri::i64s(sv.flat_region[ri::R_REGIONKEY as int]) }
pub open spec fn r_name(sv: StoresView, e: int) -> Seq<u8> {
    text_at(ri::text_view(sv.flat_region, ri::R_NAME_OFFSETS as int, ri::R_NAME_BYTES as int), e)
}

/// The tables as rows of the stored parts.
pub open spec fn line_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_l(sv), |i: int| li::row_at(sv.flat_lineitem, i)) }
pub open spec fn ord_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_o(sv), |i: int| oi::row_at(sv.flat_orders, i)) }
pub open spec fn cust_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_c(sv), |i: int| ci::row_at(sv.flat_customer, i)) }
pub open spec fn part_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_p(sv), |i: int| pi::row_at(sv.flat_part, i)) }
pub open spec fn supp_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_s(sv), |i: int| si::row_at(sv.flat_supplier, i)) }
pub open spec fn nat_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_n(sv), |i: int| ni::row_at(sv.flat_nation, i)) }
pub open spec fn reg_rows(sv: StoresView) -> Seq<Row> { Seq::new(n_r(sv), |i: int| ri::row_at(sv.flat_region, i)) }

/// The stored parts are well formed (each storage's `parts_wf` at its row count).
pub open spec fn stores_wf(sv: StoresView) -> bool {
    &&& li::parts_wf(sv.flat_lineitem, n_l(sv) as int)
    &&& oi::parts_wf(sv.flat_orders, n_o(sv) as int)
    &&& ci::parts_wf(sv.flat_customer, n_c(sv) as int)
    &&& pi::parts_wf(sv.flat_part, n_p(sv) as int)
    &&& si::parts_wf(sv.flat_supplier, n_s(sv) as int)
    &&& ni::parts_wf(sv.flat_nation, n_n(sv) as int)
    &&& ri::parts_wf(sv.flat_region, n_r(sv) as int)
}

/// The seven tables of `db` are the stored ones.
pub open spec fn tables_of(sv: StoresView, db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& db.tables[0] == line_rows(sv)
    &&& db.tables[1] == ord_rows(sv)
    &&& db.tables[2] == cust_rows(sv)
    &&& db.tables[3] == part_rows(sv)
    &&& db.tables[5] == supp_rows(sv)
    &&& db.tables[6] == nat_rows(sv)
    &&& db.tables[7] == reg_rows(sv)
}

/// The values of a key column are pairwise distinct.
pub open spec fn keys_unique(keys: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i < keys.len() && 0 <= j < keys.len() && i != j ==> keys[i] != keys[j]
}

/// The declared primary keys, as facts about the stored columns (lineitem: its rows are pairwise different).
pub open spec fn keys_ok(sv: StoresView) -> bool {
    &&& keys_unique(o_key(sv))
    &&& keys_unique(c_key(sv))
    &&& keys_unique(p_key(sv))
    &&& keys_unique(s_key(sv))
    &&& keys_unique(n_key(sv))
    &&& keys_unique(r_key(sv))
    &&& line_rows(sv).no_duplicates()
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
    &&& keys_ok(sv)
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
        rows_in_columns(line_rows(sv), ld::stored_columns_t0()),
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

proof fn lemma_ord_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[1] == ord_rows(sv), oi::parts_wf(sv.flat_orders, n_o(sv) as int),
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
    assert(t =~= ord_rows(sv)) by {
        assert forall|a: int| 0 <= a < t.len() implies #[trigger] t[a] == oi::row_at(sv.flat_orders, a) by {
            assert(rels[0][a] == oi::row_at(sv.flat_orders, a));
        }
    }
}

proof fn lemma_cust_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[2] == cust_rows(sv), ci::parts_wf(sv.flat_customer, n_c(sv) as int),
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
    assert(t =~= cust_rows(sv)) by {
        assert forall|a: int| 0 <= a < t.len() implies #[trigger] t[a] == ci::row_at(sv.flat_customer, a) by {
            assert(rels[0][a] == ci::row_at(sv.flat_customer, a));
        }
    }
}

proof fn lemma_part_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[3] == part_rows(sv), pi::parts_wf(sv.flat_part, n_p(sv) as int),
{
    let rels = pd::stored_relations(db);
    pd::lemma_declared_schema();
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

proof fn lemma_supp_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[5] == supp_rows(sv), si::parts_wf(sv.flat_supplier, n_s(sv) as int),
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

proof fn lemma_reg_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[7] == reg_rows(sv), ri::parts_wf(sv.flat_region, n_r(sv) as int),
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
    assert(t =~= reg_rows(sv)) by {
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
    lemma_line_table(sv, db);
    lemma_ord_table(sv, db);
    lemma_cust_table(sv, db);
    lemma_part_table(sv, db);
    lemma_supp_table(sv, db);
    lemma_nat_table(sv, db);
    lemma_reg_table(sv, db);
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
    assert forall|i: int, j: int| 0 <= i < keys.len() && 0 <= j < keys.len() && i != j implies keys[i] != keys[j] by {
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

/// PRIMARY KEY (l_orderkey, l_linenumber): two equal lineitem rows are the same row.
proof fn lemma_line_nodup(sv: StoresView, db: Database)
    requires bound_db(sv, db), tables_of(sv, db),
    ensures line_rows(sv).no_duplicates(),
{
    let ddb = declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    let cols = seq![0nat, 3nat];
    assert(declared_schema()[0].constraints[0] == (Constraint::Key { cols, primary: true, nulls_distinct: true }));
    let rows = line_rows(sv);
    assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && i != j implies rows[i] != rows[j] by {
        if rows[i] == rows[j] {
            assert(ddb.tables == db.tables);
            let ki = key_of(ddb.tables[0][i], cols);
            let kj = key_of(ddb.tables[0][j], cols);
            assert(ki =~= kj);
            lemma_row_not_distinct_refl(ki);
            lemma_primary_key_identifies(ddb, 0, 0, cols, true, i, j);
        }
    }
}

/// The primary keys of the seven tables hold on the stored columns.
pub proof fn lemma_keys(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures keys_ok(sv),
{
    lemma_tables(sv, db);
    crate::gendb_constraints::lemma_declared_schema();
    let k0 = Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true };
    assert(declared_schema()[1].constraints[0] == k0);
    assert(declared_schema()[2].constraints[0] == k0);
    assert(declared_schema()[3].constraints[0] == k0);
    assert(declared_schema()[5].constraints[0] == k0);
    assert(declared_schema()[6].constraints[0] == k0);
    assert(declared_schema()[7].constraints[0] == k0);
    assert forall|i: int| 0 <= i < o_key(sv).len() implies #[trigger] db.tables[1][i].len() > 0 && db.tables[1][i][0] == Val::Int(o_key(sv)[i] as int) by {
        assert(db.tables[1][i] == oi::row_at(sv.flat_orders, i));
    }
    lemma_single_key(db, 1, o_key(sv));
    assert forall|i: int| 0 <= i < c_key(sv).len() implies #[trigger] db.tables[2][i].len() > 0 && db.tables[2][i][0] == Val::Int(c_key(sv)[i] as int) by {
        assert(db.tables[2][i] == ci::row_at(sv.flat_customer, i));
    }
    lemma_single_key(db, 2, c_key(sv));
    assert forall|i: int| 0 <= i < p_key(sv).len() implies #[trigger] db.tables[3][i].len() > 0 && db.tables[3][i][0] == Val::Int(p_key(sv)[i] as int) by {
        assert(db.tables[3][i] == pi::row_at(sv.flat_part, i));
    }
    lemma_single_key(db, 3, p_key(sv));
    assert forall|i: int| 0 <= i < s_key(sv).len() implies #[trigger] db.tables[5][i].len() > 0 && db.tables[5][i][0] == Val::Int(s_key(sv)[i] as int) by {
        assert(db.tables[5][i] == si::row_at(sv.flat_supplier, i));
    }
    lemma_single_key(db, 5, s_key(sv));
    assert forall|i: int| 0 <= i < n_key(sv).len() implies #[trigger] db.tables[6][i].len() > 0 && db.tables[6][i][0] == Val::Int(n_key(sv)[i] as int) by {
        assert(db.tables[6][i] == ni::row_at(sv.flat_nation, i));
    }
    lemma_single_key(db, 6, n_key(sv));
    assert forall|i: int| 0 <= i < r_key(sv).len() implies #[trigger] db.tables[7][i].len() > 0 && db.tables[7][i][0] == Val::Int(r_key(sv)[i] as int) by {
        assert(db.tables[7][i] == ri::row_at(sv.flat_region, i));
    }
    lemma_single_key(db, 7, r_key(sv));
    lemma_line_nodup(sv, db);
}

/// The declared numeric(15,2) types bound the stored price and discount coefficients.
pub proof fn lemma_domains(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures domains_ok(sv),
{
    lemma_line_table(sv, db);
    let cs = ld::stored_columns_t0();
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
    assert forall|i: int| 0 <= i < n_l(sv) implies num15(#[trigger] l_price(sv)[i]) && num15(l_disc(sv)[i]) by {
        let r = line_rows(sv)[i];
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
    lemma_keys(sv, db);
    lemma_domains(sv, db);
}

} // verus!
