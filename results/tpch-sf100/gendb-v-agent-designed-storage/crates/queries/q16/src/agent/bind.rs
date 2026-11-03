//! What a database bound to the stored parts (`gendb_entry::bound_db`) gives the plan: its three tables are the
//! stored relations (every column is stored, in canonical order), the parts determine them (every bound database has
//! the same tables, `lemma_bound_same`), the declared primary keys make part and supplier keys unique, and the
//! declared foreign key gives every partsupp row's suppkey a supplier row (`lemma_bound`). Adapted from the admitted
//! Q2 package.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::Constraint;
use crate::spec::constraints::{constraints_hold, key_of, has_null, key_matches};
use crate::spec::typing::{db_wf, row_in_table};
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::{proj, proj_all};
use crate::link::source::rows_in_columns;
use crate::stores::custpart::interface as cpi;
use crate::stores::suppliers::interface as spi;
use crate::stores::psrun::interface as pri;
use crate::stores::supp_trisig::interface as sti;
use crate::stores::custpart::declaration as cpd;
use crate::stores::suppliers::declaration as spd;
use super::tables::Tabs;
use super::sqlrel::tabs_of;

verus! {

/// Projecting rows of `w` values on the columns `0, 1, ..., w - 1` keeps them.
proof fn lemma_proj_full(rows: Seq<Row>, cols: Seq<nat>, w: nat)
    requires
        cols.len() == w,
        forall|k: int| 0 <= k < w ==> #[trigger] cols[k] == k,
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() == w,
    ensures proj_all(rows, cols) == rows,
{
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] proj_all(rows, cols)[i] == rows[i] by {
        assert(proj(rows[i], cols) =~= rows[i]);
    }
    assert(proj_all(rows, cols) =~= rows);
}

/// The custpart and suppliers stored relations of a database.
pub open spec fn cr_of(db: Database) -> Seq<Seq<Row>> {
    cpd::stored_relations(db)
}

pub open spec fn sr_of(db: Database) -> Seq<Seq<Row>> {
    spd::stored_relations(db)
}

/// Part keys and supplier keys identify their rows.
pub open spec fn keys_unique(t: Tabs) -> bool {
    &&& forall|i: int, j: int| 0 <= i < t.p.len() && 0 <= j < t.p.len() && #[trigger] t.p[i][0] == #[trigger] t.p[j][0] ==> i == j
    &&& forall|i: int, j: int| 0 <= i < t.s.len() && 0 <= j < t.s.len() && #[trigger] t.s[i][0] == #[trigger] t.s[j][0] ==> i == j
}

/// Some supplier row has key `v`.
pub open spec fn has_supp(t: Tabs, v: Val) -> bool {
    exists|r: int| 0 <= r < t.s.len() && #[trigger] t.s[r][0] == v
}

/// Every partsupp row's suppkey is some supplier row's key.
pub open spec fn fk_supp(t: Tabs) -> bool {
    forall|i: int| 0 <= i < t.ps.len() ==> #[trigger] has_supp(t, t.ps[i][1])
}

/// A declared primary key identifies its row.
proof fn lemma_pk(db: Database, t: int, cols: Seq<nat>, i: int, j: int)
    requires
        constraints_hold(declared_db(db)),
        db.tables.len() == 8,
        0 <= t < 8,
        declared_schema()[t].constraints.len() > 0,
        declared_schema()[t].constraints[0] == (Constraint::Key { cols, primary: true, nulls_distinct: true }),
        0 <= i < db.tables[t].len(), 0 <= j < db.tables[t].len(),
        key_of(db.tables[t][i], cols) == key_of(db.tables[t][j], cols),
    ensures i == j,
{
    crate::gendb_constraints::lemma_declared_schema();
    let ddb = declared_db(db);
    crate::bridge::equality::lemma_row_not_distinct_refl(key_of(db.tables[t][i], cols));
    crate::bridge::constraints::lemma_primary_key_identifies(ddb, t, 0, cols, true, i, j);
}

/// A table whose first constraint is a primary key on column 0: equal keys are one row.
proof fn lemma_pk0(db: Database, t: int)
    requires
        constraints_hold(declared_db(db)),
        db.tables.len() == 8,
        0 <= t < 8,
        declared_schema()[t].constraints.len() > 0,
        declared_schema()[t].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }),
        forall|i: int| 0 <= i < db.tables[t].len() ==> (#[trigger] db.tables[t][i]).len() > 0,
    ensures
        forall|i: int, j: int| 0 <= i < db.tables[t].len() && 0 <= j < db.tables[t].len()
            && #[trigger] db.tables[t][i][0] == #[trigger] db.tables[t][j][0] ==> i == j,
{
    let rows = db.tables[t];
    assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && #[trigger] rows[i][0] == #[trigger] rows[j][0]
        implies i == j by {
        assert(key_of(rows[i], seq![0nat]) =~= key_of(rows[j], seq![0nat]));
        lemma_pk(db, t, seq![0nat], i, j);
    }
}

/// The declared foreign key `partsupp(ps_suppkey) -> supplier(s_suppkey)`.
proof fn lemma_fk_supp(db: Database)
    requires
        constraints_hold(declared_db(db)),
        db.tables.len() == 8,
        db.schema == schema_spec(),
        forall|i: int| 0 <= i < db.tables[4].len() ==> (#[trigger] db.tables[4][i]).len() == 5 && db.tables[4][i][1] is Int,
        forall|r: int| 0 <= r < db.tables[5].len() ==> (#[trigger] db.tables[5][r]).len() == 7 && db.tables[5][r][0] is Int,
    ensures fk_supp(tabs_of(db)),
{
    crate::gendb_constraints::lemma_declared_schema();
    let ddb = declared_db(db);
    assert(declared_schema()[4].constraints[2]
        == (Constraint::ForeignKey { cols: seq![1nat], table: 5, ref_cols: seq![0nat], match_full: false }));
    let t = tabs_of(db);
    assert forall|i: int| 0 <= i < t.ps.len() implies #[trigger] has_supp(t, t.ps[i][1]) by {
        let k = key_of(db.tables[4][i], seq![1nat]);
        assert(k =~= seq![db.tables[4][i][1]]);
        assert(!has_null(k)) by {
            if has_null(k) {
                let q = choose|q: int| 0 <= q < k.len() && (#[trigger] k[q]) is Null;
                assert(q == 0);
            }
        }
        crate::bridge::constraints::lemma_foreign_key_target(ddb, 4, 2, seq![1nat], 5, seq![0nat], false, i);
        let r = choose|r: int| 0 <= r < ddb.tables[5].len() && key_matches(k, key_of(#[trigger] ddb.tables[5][r], seq![0nat]));
        let m = key_of(db.tables[5][r], seq![0nat]);
        assert(m =~= seq![db.tables[5][r][0]]);
        assert(crate::spec::scalar::compare(k[0], m[0]) == Some(0int));
        assert(t.s[r][0] == t.ps[i][1]);
        assert(has_supp(t, t.ps[i][1]));
    }
}

/// psrun's stored relations are suppliers' (the same declaration).
proof fn lemma_same_relations(db: Database)
    ensures crate::stores::psrun::declaration::stored_relations(db) == spd::stored_relations(db),
{
    assert(crate::stores::psrun::declaration::stored_cols_t0() =~= spd::stored_cols_t0());
    assert(crate::stores::psrun::declaration::stored_cols_t1() =~= spd::stored_cols_t1());
    assert(crate::stores::psrun::declaration::stored_cols_t2() =~= spd::stored_cols_t2());
    assert(crate::stores::psrun::declaration::stored_cols_t3() =~= spd::stored_cols_t3());
    assert(crate::stores::psrun::declaration::stored_relations(db) =~= spd::stored_relations(db));
}

/// supp_trisig's stored relations are suppliers' (the same declaration).
proof fn lemma_same_relations_sig(db: Database)
    ensures crate::stores::supp_trisig::declaration::stored_relations(db) == spd::stored_relations(db),
{
    assert(crate::stores::supp_trisig::declaration::stored_cols_t0() =~= spd::stored_cols_t0());
    assert(crate::stores::supp_trisig::declaration::stored_cols_t1() =~= spd::stored_cols_t1());
    assert(crate::stores::supp_trisig::declaration::stored_cols_t2() =~= spd::stored_cols_t2());
    assert(crate::stores::supp_trisig::declaration::stored_cols_t3() =~= spd::stored_cols_t3());
    assert(crate::stores::supp_trisig::declaration::stored_relations(db) =~= spd::stored_relations(db));
}

/// The facts of a bound database.
pub proof fn lemma_bound(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        db.tables.len() == 8,
        cpi::represents(sv.custpart, cr_of(db)),
        spi::represents(sv.suppliers, sr_of(db)),
        pri::represents(sv.psrun, sr_of(db)),
        sti::represents(sv.supp_trisig, sr_of(db)),
        rows_in_columns(cr_of(db)[1], cpd::stored_columns_t1()),
        rows_in_columns(sr_of(db)[0], spd::stored_columns_t0()),
        rows_in_columns(sr_of(db)[1], spd::stored_columns_t1()),
        tabs_of(db) == (Tabs { p: cr_of(db)[1], ps: sr_of(db)[0], s: sr_of(db)[1] }),
        cr_of(db)[1] == db.tables[3],
        keys_unique(tabs_of(db)),
        fk_supp(tabs_of(db)),
{
    cpd::lemma_declared_schema();
    spd::lemma_declared_schema();
    cpd::lemma_stored_relations(db);
    spd::lemma_stored_relations(db);
    lemma_same_relations(db);
    lemma_same_relations_sig(db);
    crate::gendb_constraints::lemma_declared_schema();
    assert(db.tables.len() == 8);
    // Widths of the three tables' rows (db_wf).
    assert forall|t: int, i: int| 3 <= t < 6 && 0 <= i < db.tables[t].len()
        implies (#[trigger] db.tables[t][i]).len() == schema_spec()[t].columns.len() by {
        assert(row_in_table(db.tables[t][i], db.schema[t]));
    }
    lemma_proj_full(db.tables[3], cpd::stored_cols_t1(), 9);
    lemma_proj_full(db.tables[4], spd::stored_cols_t0(), 5);
    lemma_proj_full(db.tables[5], spd::stored_cols_t1(), 7);
    assert(declared_schema()[3].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[5].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    lemma_pk0(db, 3);
    lemma_pk0(db, 5);
    // Types of the key columns the foreign key compares (rows_in_columns of the stored relations).
    let sr = sr_of(db);
    assert forall|i: int| 0 <= i < db.tables[4].len() implies (#[trigger] db.tables[4][i]).len() == 5 && db.tables[4][i][1] is Int by {
        assert(sr[0][i] == db.tables[4][i]);
        assert(crate::spec::typing::value_in_column(sr[0][i][1], spd::stored_columns_t0()[1]));
    }
    assert forall|r: int| 0 <= r < db.tables[5].len() implies (#[trigger] db.tables[5][r]).len() == 7 && db.tables[5][r][0] is Int by {
        assert(sr[1][r] == db.tables[5][r]);
        assert(crate::spec::typing::value_in_column(sr[1][r][0], spd::stored_columns_t1()[0]));
    }
    lemma_fk_supp(db);
}

/// Every database bound to the same parts has the same three tables.
pub proof fn lemma_bound_same(sv: StoresView, db1: Database, db2: Database)
    requires bound_db(sv, db1), bound_db(sv, db2),
    ensures tabs_of(db1) == tabs_of(db2), db1.tables.len() == 8, db2.tables.len() == 8,
{
    lemma_bound(sv, db1);
    lemma_bound(sv, db2);
    cpi::lemma_represents_determines(sv.custpart, cr_of(db1), cr_of(db2));
    spi::lemma_represents_determines(sv.suppliers, sr_of(db1), sr_of(db2));
}

} // verus!
