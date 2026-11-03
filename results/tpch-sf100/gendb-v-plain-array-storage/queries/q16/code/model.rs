//! The three tables this query reads, as functions of the stored parts (`StoresView`): table `t` of every database
//! bound to the parts is exactly `<t>_rows(sv)` (`lemma_tables`), so all later reasoning is about the stored
//! arrays. The declared primary keys of `part` and `supplier` make their key columns duplicate-free, and the
//! foreign key `partsupp.ps_suppkey -> supplier.s_suppkey` puts every supplier key of `partsupp` in the supplier
//! key column (`lemma_keys`).
//!
//! Table ids (schema order): 3 part (9 columns), 4 partsupp (5 columns), 5 supplier (7 columns).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::typing::*;
use crate::spec::types::*;
use crate::spec::scalar::compare;
use crate::spec::constraints::*;
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::{proj, proj_all, text_at};
use crate::link::source::lemma_proj_all_index;
use crate::bridge::constraints::{lemma_primary_key_identifies, lemma_foreign_key_target};
use crate::bridge::equality::lemma_row_not_distinct_refl;
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_partsupp::interface as psi;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_part::declaration as pd;
use crate::stores::flat_partsupp::declaration as psd;
use crate::stores::flat_supplier::declaration as sd;

verus! {

// ------------------------------------------------------------------------------------------ stored columns

/// Row counts.
pub open spec fn part_n(sv: StoresView) -> nat { pi::i64s(sv.flat_part[pi::P_PARTKEY as int]).len() }
pub open spec fn ps_n(sv: StoresView) -> nat { psi::i64s(sv.flat_partsupp[psi::PS_PARTKEY as int]).len() }
pub open spec fn supp_n(sv: StoresView) -> nat { si::i64s(sv.flat_supplier[si::S_SUPPKEY as int]).len() }

/// Integer columns (as stored).
pub open spec fn p_keys(sv: StoresView) -> Seq<i64> { pi::i64s(sv.flat_part[pi::P_PARTKEY as int]) }
pub open spec fn p_sizes(sv: StoresView) -> Seq<i64> { pi::i64s(sv.flat_part[pi::P_SIZE as int]) }
pub open spec fn ps_pkeys(sv: StoresView) -> Seq<i64> { psi::i64s(sv.flat_partsupp[psi::PS_PARTKEY as int]) }
pub open spec fn ps_skeys(sv: StoresView) -> Seq<i64> { psi::i64s(sv.flat_partsupp[psi::PS_SUPPKEY as int]) }
pub open spec fn s_keys(sv: StoresView) -> Seq<i64> { si::i64s(sv.flat_supplier[si::S_SUPPKEY as int]) }

/// Text columns, as views and as the bytes of one row.
pub open spec fn brand_view(sv: StoresView) -> crate::link::query::TextView {
    pi::text_view(sv.flat_part, pi::P_BRAND_OFFSETS as int, pi::P_BRAND_BYTES as int)
}
pub open spec fn type_view(sv: StoresView) -> crate::link::query::TextView {
    pi::text_view(sv.flat_part, pi::P_TYPE_OFFSETS as int, pi::P_TYPE_BYTES as int)
}
pub open spec fn comment_view(sv: StoresView) -> crate::link::query::TextView {
    si::text_view(sv.flat_supplier, si::S_COMMENT_OFFSETS as int, si::S_COMMENT_BYTES as int)
}
pub open spec fn p_brand(sv: StoresView, a: int) -> Seq<u8> { text_at(brand_view(sv), a) }
pub open spec fn p_type(sv: StoresView, a: int) -> Seq<u8> { text_at(type_view(sv), a) }
pub open spec fn s_comment(sv: StoresView, b: int) -> Seq<u8> { text_at(comment_view(sv), b) }

/// The tables as rows of the stored parts.
pub open spec fn part_rows(sv: StoresView) -> Seq<Row> { Seq::new(part_n(sv), |a: int| pi::row_at(sv.flat_part, a)) }
pub open spec fn ps_rows(sv: StoresView) -> Seq<Row> { Seq::new(ps_n(sv), |c: int| psi::row_at(sv.flat_partsupp, c)) }
pub open spec fn supp_rows(sv: StoresView) -> Seq<Row> { Seq::new(supp_n(sv), |b: int| si::row_at(sv.flat_supplier, b)) }

/// The stored parts are well formed (each storage's `parts_wf` at its row count).
pub open spec fn stores_wf(sv: StoresView) -> bool {
    &&& pi::parts_wf(sv.flat_part, part_n(sv) as int)
    &&& psi::parts_wf(sv.flat_partsupp, ps_n(sv) as int)
    &&& si::parts_wf(sv.flat_supplier, supp_n(sv) as int)
}

/// The three tables of `db` are the stored ones.
pub open spec fn tables_of(sv: StoresView, db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& db.tables[3] == part_rows(sv)
    &&& db.tables[4] == ps_rows(sv)
    &&& db.tables[5] == supp_rows(sv)
}

/// No key occurs twice.
pub open spec fn keys_unique(keys: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i < keys.len() && 0 <= j < keys.len() && i != j ==> keys[i] != keys[j]
}

/// `k` is the key of some supplier row.
pub open spec fn is_supplier(sv: StoresView, k: int) -> bool {
    exists|b: int| 0 <= b < supp_n(sv) && s_keys(sv)[b] == k
}

/// The declared keys, as facts about the stored key columns: part and supplier keys are duplicate-free, and every
/// supplier key of `partsupp` is the key of some supplier row.
pub open spec fn keys_ok(sv: StoresView) -> bool {
    &&& keys_unique(p_keys(sv))
    &&& keys_unique(s_keys(sv))
    &&& forall|c: int| 0 <= c < ps_n(sv) ==> #[trigger] is_supplier(sv, ps_skeys(sv)[c] as int)
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

/// Every database bound to the parts has the stored tables, and the parts are well formed.
pub proof fn lemma_tables(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures tables_of(sv, db), stores_wf(sv),
{
    lemma_part_table(sv, db);
    lemma_ps_table(sv, db);
    lemma_supp_table(sv, db);
}

// ------------------------------------------------------------------------------------------ declared keys

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

/// The foreign key `partsupp(ps_suppkey) -> supplier(s_suppkey)` on the stored columns.
proof fn lemma_supp_fk(sv: StoresView, db: Database)
    requires bound_db(sv, db), tables_of(sv, db), stores_wf(sv),
    ensures forall|c: int| 0 <= c < ps_n(sv) ==> #[trigger] is_supplier(sv, ps_skeys(sv)[c] as int),
{
    let ddb = declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    let fk = Constraint::ForeignKey { cols: seq![1nat], table: 5, ref_cols: seq![0nat], match_full: false };
    assert(declared_schema()[4].constraints[2] == fk);
    assert forall|c: int| 0 <= c < ps_n(sv) implies #[trigger] is_supplier(sv, ps_skeys(sv)[c] as int) by {
        let r = ddb.tables[4][c];
        assert(r == psi::row_at(sv.flat_partsupp, c));
        let k = key_of(r, seq![1nat]);
        assert(k =~= seq![Val::Int(ps_skeys(sv)[c] as int)]);
        assert(!has_null(k));
        lemma_foreign_key_target(ddb, 4, 2, seq![1nat], 5, seq![0nat], false, c);
        let b = choose|j: int| 0 <= j < ddb.tables[5].len() && key_matches(k, key_of(#[trigger] ddb.tables[5][j], seq![0nat]));
        let sr = ddb.tables[5][b];
        assert(sr == si::row_at(sv.flat_supplier, b));
        let m = key_of(sr, seq![0nat]);
        assert(m =~= seq![Val::Int(s_keys(sv)[b] as int)]);
        assert(compare(k[0], m[0]) == Some(0int));
        assert(s_keys(sv)[b] == ps_skeys(sv)[c]);
    }
}

/// The declared keys hold on the stored key columns of every bound database.
pub proof fn lemma_keys(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures keys_ok(sv),
{
    lemma_tables(sv, db);
    crate::gendb_constraints::lemma_declared_schema();
    assert(declared_schema()[3].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[5].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    lemma_single_key(db, 3, p_keys(sv));
    lemma_single_key(db, 5, s_keys(sv));
    lemma_supp_fk(sv, db);
}

} // verus!
