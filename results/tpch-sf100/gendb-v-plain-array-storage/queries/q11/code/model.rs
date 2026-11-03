//! The three tables this query reads, as functions of the stored parts (`StoresView`): table `t` of every database
//! bound to the parts is exactly `<t>_rows(sv)` (`lemma_tables`), so all later reasoning is about the stored
//! arrays. The declared primary keys of `supplier` and `nation` make their key columns duplicate-free
//! (`lemma_keys`), and the declared column types bound the stored values (`lemma_bounds`).
//!
//! Table ids (schema order): 4 partsupp (5 columns), 5 supplier (7 columns), 6 nation (4 columns).
//!
//! The qualification of a partsupp row (`qrow`): some supplier row has its supplier key and lies in a nation row
//! whose name is the parameter `$1` (`supp_ok`, `nat_ok`). The value of a row is `ps_supplycost * ps_availqty`
//! as an exact integer at scale 2 (`val`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::numeric::*;
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
use crate::stores::flat_partsupp::interface as psi;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_partsupp::declaration as psd;
use crate::stores::flat_supplier::declaration as sd;
use crate::stores::flat_nation::declaration as nd;

verus! {

// ------------------------------------------------------------------------------------------ stored columns

/// Row counts.
pub open spec fn ps_n(sv: StoresView) -> nat { psi::i64s(sv.flat_partsupp[psi::PS_PARTKEY as int]).len() }
pub open spec fn supp_n(sv: StoresView) -> nat { si::i64s(sv.flat_supplier[si::S_SUPPKEY as int]).len() }
pub open spec fn nat_n(sv: StoresView) -> nat { ni::i64s(sv.flat_nation[ni::N_NATIONKEY as int]).len() }

/// The stored columns the query reads.
pub open spec fn ps_pkeys(sv: StoresView) -> Seq<i64> { psi::i64s(sv.flat_partsupp[psi::PS_PARTKEY as int]) }
pub open spec fn ps_skeys(sv: StoresView) -> Seq<i64> { psi::i64s(sv.flat_partsupp[psi::PS_SUPPKEY as int]) }
pub open spec fn ps_aqs(sv: StoresView) -> Seq<i64> { psi::i64s(sv.flat_partsupp[psi::PS_AVAILQTY as int]) }
pub open spec fn ps_costs(sv: StoresView) -> Seq<i128> { psi::i128s(sv.flat_partsupp[psi::PS_SUPPLYCOST as int]) }
pub open spec fn s_keys(sv: StoresView) -> Seq<i64> { si::i64s(sv.flat_supplier[si::S_SUPPKEY as int]) }
pub open spec fn s_nks(sv: StoresView) -> Seq<i64> { si::i64s(sv.flat_supplier[si::S_NATIONKEY as int]) }
pub open spec fn n_keys(sv: StoresView) -> Seq<i64> { ni::i64s(sv.flat_nation[ni::N_NATIONKEY as int]) }
pub open spec fn n_name_view(sv: StoresView) -> crate::link::query::TextView {
    ni::text_view(sv.flat_nation, ni::N_NAME_OFFSETS as int, ni::N_NAME_BYTES as int)
}
pub open spec fn n_name(sv: StoresView, d: int) -> Seq<u8> { text_at(n_name_view(sv), d) }

/// The tables as rows of the stored parts.
pub open spec fn ps_rows(sv: StoresView) -> Seq<Row> { Seq::new(ps_n(sv), |c: int| psi::row_at(sv.flat_partsupp, c)) }
pub open spec fn supp_rows(sv: StoresView) -> Seq<Row> { Seq::new(supp_n(sv), |b: int| si::row_at(sv.flat_supplier, b)) }
pub open spec fn nat_rows(sv: StoresView) -> Seq<Row> { Seq::new(nat_n(sv), |d: int| ni::row_at(sv.flat_nation, d)) }

/// The stored parts are well formed (each storage's `parts_wf` at its row count).
pub open spec fn stores_wf(sv: StoresView) -> bool {
    &&& psi::parts_wf(sv.flat_partsupp, ps_n(sv) as int)
    &&& si::parts_wf(sv.flat_supplier, supp_n(sv) as int)
    &&& ni::parts_wf(sv.flat_nation, nat_n(sv) as int)
}

/// The three tables of `db` are the stored ones.
pub open spec fn tables_of(sv: StoresView, db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& db.tables[4] == ps_rows(sv)
    &&& db.tables[5] == supp_rows(sv)
    &&& db.tables[6] == nat_rows(sv)
}

/// Pairwise distinct keys.
pub open spec fn keys_unique(keys: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i < keys.len() && 0 <= j < keys.len() && i != j ==> keys[i] != keys[j]
}

/// The declared primary keys of supplier and nation, as facts about the stored key columns.
pub open spec fn keys_ok(sv: StoresView) -> bool {
    &&& keys_unique(s_keys(sv))
    &&& keys_unique(n_keys(sv))
}

/// `10^15`: the bound of a `numeric(15, 2)` coefficient.
pub open spec fn cost_bound() -> int { 1_000_000_000_000_000 }

/// The declared column domain of `ps_supplycost` (numeric(15,2)) on the stored coefficients.
pub open spec fn bounds_ok(sv: StoresView) -> bool {
    forall|c: int| 0 <= c < ps_n(sv) ==> -cost_bound() < #[trigger] ps_costs(sv)[c] < cost_bound()
}

// ------------------------------------------------------------------------------------------ qualification

/// Nation row `d` is named `p`.
pub open spec fn nat_ok(sv: StoresView, p: Seq<u8>, d: int) -> bool {
    n_name(sv, d) == p
}

/// Supplier row `b` lies in a nation named `p`.
pub open spec fn supp_ok(sv: StoresView, p: Seq<u8>, b: int) -> bool {
    exists|d: int| 0 <= d < nat_n(sv) && #[trigger] n_keys(sv)[d] == s_nks(sv)[b] && nat_ok(sv, p, d)
}

/// Some supplier of a nation named `p` has the supplier key `k`.
pub open spec fn key_ok(sv: StoresView, p: Seq<u8>, k: int) -> bool {
    exists|b: int| 0 <= b < supp_n(sv) && #[trigger] s_keys(sv)[b] == k && supp_ok(sv, p, b)
}

/// Partsupp row `c` qualifies: its supplier lies in a nation named `p`.
pub open spec fn qrow(sv: StoresView, p: Seq<u8>, c: int) -> bool {
    key_ok(sv, p, ps_skeys(sv)[c] as int)
}

/// The exact value `ps_supplycost * ps_availqty` of partsupp row `c` (coefficient at scale 2).
pub open spec fn val(sv: StoresView, c: int) -> int {
    ps_costs(sv)[c] as int * ps_aqs(sv)[c] as int
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

proof fn lemma_ps_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db.tables[4] == ps_rows(sv), psi::parts_wf(sv.flat_partsupp, ps_n(sv) as int), db.tables.len() == 8,
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

/// Every database bound to the parts has the stored tables, and the parts are well formed.
pub proof fn lemma_tables(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures tables_of(sv, db), stores_wf(sv),
{
    lemma_ps_table(sv, db);
    lemma_supp_table(sv, db);
    lemma_nat_table(sv, db);
}

// ------------------------------------------------------------------------------------------ primary keys

/// A single-column primary key of table `t` makes its stored key column duplicate-free.
proof fn lemma_single_key(db: Database, t: int, keys: Seq<i64>)
    requires
        constraints_hold(declared_db(db)),
        db.tables.len() == 8,
        4 <= t < 8,
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

/// The primary keys of supplier and nation hold on the stored key columns.
pub proof fn lemma_keys(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures keys_ok(sv),
{
    lemma_tables(sv, db);
    crate::gendb_constraints::lemma_declared_schema();
    assert(declared_schema()[5].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[6].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    lemma_single_key(db, 5, s_keys(sv));
    lemma_single_key(db, 6, n_keys(sv));
}

// ------------------------------------------------------------------------------------------ column domains

/// The stored supply costs lie in the declared `numeric(15, 2)` domain.
pub proof fn lemma_bounds(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures bounds_ok(sv),
{
    lemma_tables(sv, db);
    assert(schema_spec()[4].columns[3] == Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }) by (compute);
    assert(pow10(15) == cost_bound()) by (compute);
    assert forall|c: int| 0 <= c < ps_n(sv) implies -cost_bound() < #[trigger] ps_costs(sv)[c] < cost_bound() by {
        let r = db.tables[4][c];
        assert(r == psi::row_at(sv.flat_partsupp, c));
        assert(row_in_table(r, db.schema[4]));
        assert(value_in_column(r[3], db.schema[4].columns[3]));
        assert(r[3] == Val::Num { coeff: ps_costs(sv)[c] as int, scale: 2 });
    }
}

} // verus!
