//! The five tables this query reads, as functions of the stored parts (`StoresView`): table `t` of every database
//! bound to the parts is exactly `<t>_rows(sv)` (`lemma_tables`), so all later reasoning is about the stored
//! arrays. The declared primary keys give key uniqueness of each table as facts about those arrays
//! (`lemma_keys`).
//!
//! Table ids (schema order): 3 part, 4 partsupp, 5 supplier, 6 nation, 7 region.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::constraints::*;
use crate::spec::equality::*;
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::{proj, proj_all, text_at};
use crate::link::source::lemma_proj_all_index;
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::bridge::equality::lemma_row_not_distinct_refl;
use crate::agent::scan_part::keys_unique;
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_partsupp::interface as psi;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_region::interface as ri;
use crate::stores::flat_part::declaration as pd;
use crate::stores::flat_partsupp::declaration as psd;
use crate::stores::flat_supplier::declaration as sd;
use crate::stores::flat_nation::declaration as nd;
use crate::stores::flat_region::declaration as rd;

verus! {

// ------------------------------------------------------------------------------------------ stored columns

/// Row counts.
pub open spec fn part_n(sv: StoresView) -> nat { pi::i64s(sv.flat_part[pi::P_PARTKEY as int]).len() }
pub open spec fn ps_n(sv: StoresView) -> nat { psi::i64s(sv.flat_partsupp[psi::PS_PARTKEY as int]).len() }
pub open spec fn supp_n(sv: StoresView) -> nat { si::i64s(sv.flat_supplier[si::S_SUPPKEY as int]).len() }
pub open spec fn nat_n(sv: StoresView) -> nat { ni::i64s(sv.flat_nation[ni::N_NATIONKEY as int]).len() }
pub open spec fn reg_n(sv: StoresView) -> nat { ri::i64s(sv.flat_region[ri::R_REGIONKEY as int]).len() }

/// Key columns (as stored).
pub open spec fn p_keys(sv: StoresView) -> Seq<i64> { pi::i64s(sv.flat_part[pi::P_PARTKEY as int]) }
pub open spec fn ps_pkeys(sv: StoresView) -> Seq<i64> { psi::i64s(sv.flat_partsupp[psi::PS_PARTKEY as int]) }
pub open spec fn ps_skeys(sv: StoresView) -> Seq<i64> { psi::i64s(sv.flat_partsupp[psi::PS_SUPPKEY as int]) }
pub open spec fn s_keys(sv: StoresView) -> Seq<i64> { si::i64s(sv.flat_supplier[si::S_SUPPKEY as int]) }
pub open spec fn n_keys(sv: StoresView) -> Seq<i64> { ni::i64s(sv.flat_nation[ni::N_NATIONKEY as int]) }
pub open spec fn r_keys(sv: StoresView) -> Seq<i64> { ri::i64s(sv.flat_region[ri::R_REGIONKEY as int]) }

/// Other stored columns the query reads.
pub open spec fn p_sizes(sv: StoresView) -> Seq<i64> { pi::i64s(sv.flat_part[pi::P_SIZE as int]) }
pub open spec fn p_type(sv: StoresView, a: int) -> Seq<u8> {
    text_at(pi::text_view(sv.flat_part, pi::P_TYPE_OFFSETS as int, pi::P_TYPE_BYTES as int), a)
}
pub open spec fn ps_costs(sv: StoresView) -> Seq<i128> { psi::i128s(sv.flat_partsupp[psi::PS_SUPPLYCOST as int]) }
pub open spec fn s_nks(sv: StoresView) -> Seq<i64> { si::i64s(sv.flat_supplier[si::S_NATIONKEY as int]) }
pub open spec fn s_accts(sv: StoresView) -> Seq<i128> { si::i128s(sv.flat_supplier[si::S_ACCTBAL as int]) }
pub open spec fn n_rks(sv: StoresView) -> Seq<i64> { ni::i64s(sv.flat_nation[ni::N_REGIONKEY as int]) }
pub open spec fn r_name(sv: StoresView, e: int) -> Seq<u8> {
    text_at(ri::text_view(sv.flat_region, ri::R_NAME_OFFSETS as int, ri::R_NAME_BYTES as int), e)
}

/// Supplier row `b` lies in a nation (row `d`) of a region (row `e`) named `rp`.
pub open spec fn supp_in_reg(sv: StoresView, rp: Seq<u8>, b: int) -> bool {
    exists|d: int, e: int| 0 <= d < nat_n(sv) && 0 <= e < reg_n(sv)
        && #[trigger] n_keys(sv)[d] == s_nks(sv)[b] && n_rks(sv)[d] == #[trigger] r_keys(sv)[e] && r_name(sv, e) == rp
}

/// Partsupp row `c` offers part key `k` from a supplier of the region (a row of the subquery for `k`).
pub open spec fn sub_ok(sv: StoresView, rp: Seq<u8>, k: int, c: int) -> bool {
    &&& ps_pkeys(sv)[c] == k
    &&& exists|b: int| 0 <= b < supp_n(sv) && #[trigger] s_keys(sv)[b] == ps_skeys(sv)[c] && supp_in_reg(sv, rp, b)
}

/// `w` is at most every supply cost of the subquery rows for part key `k`.
pub open spec fn min_ok(sv: StoresView, rp: Seq<u8>, k: int, w: int) -> bool {
    forall|c: int| 0 <= c < ps_n(sv) && #[trigger] sub_ok(sv, rp, k, c) ==> w <= ps_costs(sv)[c]
}

/// The tables as rows of the stored parts.
pub open spec fn part_rows(sv: StoresView) -> Seq<Row> { Seq::new(part_n(sv), |a: int| pi::row_at(sv.flat_part, a)) }
pub open spec fn ps_rows(sv: StoresView) -> Seq<Row> { Seq::new(ps_n(sv), |c: int| psi::row_at(sv.flat_partsupp, c)) }
pub open spec fn supp_rows(sv: StoresView) -> Seq<Row> { Seq::new(supp_n(sv), |b: int| si::row_at(sv.flat_supplier, b)) }
pub open spec fn nat_rows(sv: StoresView) -> Seq<Row> { Seq::new(nat_n(sv), |d: int| ni::row_at(sv.flat_nation, d)) }
pub open spec fn reg_rows(sv: StoresView) -> Seq<Row> { Seq::new(reg_n(sv), |e: int| ri::row_at(sv.flat_region, e)) }

/// The stored parts are well formed (each storage's `parts_wf` at its row count).
pub open spec fn stores_wf(sv: StoresView) -> bool {
    &&& pi::parts_wf(sv.flat_part, part_n(sv) as int)
    &&& psi::parts_wf(sv.flat_partsupp, ps_n(sv) as int)
    &&& si::parts_wf(sv.flat_supplier, supp_n(sv) as int)
    &&& ni::parts_wf(sv.flat_nation, nat_n(sv) as int)
    &&& ri::parts_wf(sv.flat_region, reg_n(sv) as int)
}

/// The five tables of `db` are the stored ones.
pub open spec fn tables_of(sv: StoresView, db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& db.tables[3] == part_rows(sv)
    &&& db.tables[4] == ps_rows(sv)
    &&& db.tables[5] == supp_rows(sv)
    &&& db.tables[6] == nat_rows(sv)
    &&& db.tables[7] == reg_rows(sv)
}

/// The declared primary keys, as facts about the stored key columns.
pub open spec fn keys_ok(sv: StoresView) -> bool {
    &&& keys_unique(p_keys(sv))
    &&& keys_unique(s_keys(sv))
    &&& keys_unique(n_keys(sv))
    &&& keys_unique(r_keys(sv))
    &&& forall|c1: int, c2: int| 0 <= c1 < ps_n(sv) && 0 <= c2 < ps_n(sv) && c1 != c2
        ==> #[trigger] ps_pkeys(sv)[c1] != #[trigger] ps_pkeys(sv)[c2] || ps_skeys(sv)[c1] != ps_skeys(sv)[c2]
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

proof fn lemma_part_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[3] == part_rows(sv), pi::parts_wf(sv.flat_part, part_n(sv) as int), db.tables.len() == 8,
{
    let rels = pd::stored_relations(db);
    pd::lemma_declared_schema();
    let cols = pd::stored_cols_t0();
    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {} else if k == 6 {} else if k == 7 {} else {}
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
    ensures db.tables[4] == ps_rows(sv), psi::parts_wf(sv.flat_partsupp, ps_n(sv) as int),
{
    let rels = psd::stored_relations(db);
    psd::lemma_declared_schema();
    let cols = psd::stored_cols_t0();
    assert forall|k: int| 0 <= k < cols.len() implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else {}
    }
    lemma_table_is_stored(db, 4, cols, rels[0]);
    let t = db.tables[4];
    assert(psi::represents(sv.flat_partsupp, rels));
    assert(t =~= ps_rows(sv)) by {
        assert forall|c: int| 0 <= c < t.len() implies #[trigger] t[c] == psi::row_at(sv.flat_partsupp, c) by {
            assert(rels[0][c] == psi::row_at(sv.flat_partsupp, c));
        }
    }
}

proof fn lemma_supp_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[5] == supp_rows(sv), si::parts_wf(sv.flat_supplier, supp_n(sv) as int),
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
        assert forall|b: int| 0 <= b < t.len() implies #[trigger] t[b] == si::row_at(sv.flat_supplier, b) by {
            assert(rels[0][b] == si::row_at(sv.flat_supplier, b));
        }
    }
}

proof fn lemma_nat_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[6] == nat_rows(sv), ni::parts_wf(sv.flat_nation, nat_n(sv) as int),
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
        assert forall|d: int| 0 <= d < t.len() implies #[trigger] t[d] == ni::row_at(sv.flat_nation, d) by {
            assert(rels[0][d] == ni::row_at(sv.flat_nation, d));
        }
    }
}

proof fn lemma_reg_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[7] == reg_rows(sv), ri::parts_wf(sv.flat_region, reg_n(sv) as int),
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
        assert forall|e: int| 0 <= e < t.len() implies #[trigger] t[e] == ri::row_at(sv.flat_region, e) by {
            assert(rels[0][e] == ri::row_at(sv.flat_region, e));
        }
    }
}

/// Every database bound to the parts has the stored tables, and the parts are well formed.
pub proof fn lemma_tables(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures tables_of(sv, db), stores_wf(sv),
{
    lemma_part_table(sv, db);
    lemma_ps_table(sv, db);
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
        3 <= t < 8,
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

/// The primary keys of the five tables hold on the stored key columns.
pub proof fn lemma_keys(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures keys_ok(sv),
{
    lemma_tables(sv, db);
    crate::gendb_constraints::lemma_declared_schema();
    assert(declared_schema()[3].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[5].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[6].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[7].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[4].constraints[0] == (Constraint::Key { cols: seq![0nat, 1nat], primary: true, nulls_distinct: true }));
    lemma_single_key(db, 3, p_keys(sv));
    lemma_single_key(db, 5, s_keys(sv));
    lemma_single_key(db, 6, n_keys(sv));
    lemma_single_key(db, 7, r_keys(sv));
    let ddb = declared_db(db);
    assert forall|c1: int, c2: int| 0 <= c1 < ps_n(sv) && 0 <= c2 < ps_n(sv) && c1 != c2
        implies #[trigger] ps_pkeys(sv)[c1] != #[trigger] ps_pkeys(sv)[c2] || ps_skeys(sv)[c1] != ps_skeys(sv)[c2] by {
        if ps_pkeys(sv)[c1] == ps_pkeys(sv)[c2] && ps_skeys(sv)[c1] == ps_skeys(sv)[c2] {
            let cols = seq![0nat, 1nat];
            let k1 = key_of(ddb.tables[4][c1], cols);
            let k2 = key_of(ddb.tables[4][c2], cols);
            assert(k1 =~= k2);
            lemma_row_not_distinct_refl(k1);
            lemma_primary_key_identifies(ddb, 4, 0, cols, true, c1, c2);
        }
    }
}

} // verus!
