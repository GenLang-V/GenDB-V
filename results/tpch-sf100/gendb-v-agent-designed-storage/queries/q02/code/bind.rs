//! What a database bound to the stored parts (`gendb_entry::bound_db`) gives the plan: its five tables are the
//! stored relations (every column is stored, in canonical order), the parts determine them (every bound database
//! has the same tables, `lemma_bound_same`), and the declared primary keys make them duplicate-free with unique
//! keys (`lemma_bound`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::Constraint;
use crate::spec::constraints::{constraints_hold, key_of};
use crate::spec::typing::{db_wf, row_in_table};
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::{StoresView, stored_ok};
use crate::link::query::{proj, proj_all};
use crate::link::source::rows_in_columns;
use crate::stores::custpart::interface as cpi;
use crate::stores::suppliers::interface as spi;
use crate::stores::custpart::declaration as cpd;
use crate::stores::suppliers::declaration as spd;
use crate::stores::part_sztyidx::interface as sxi;
use crate::stores::suppliers_psrun::interface as ppi;
use crate::stores::suppliers_psrun::declaration as ppd;
use crate::stores::suppliers_rank::interface as rki;
use crate::stores::suppliers_rank::declaration as rkd;
use crate::stores::part_sztyidx::declaration as sxd;
use super::tables::Tabs;
use super::q2spec::keys_unique;
use super::sqlrel::{tabs_of, tabs_nodup};

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

/// The custpart and suppliers stored relations of a bound database.
pub open spec fn cr_of(db: Database) -> Seq<Seq<Row>> {
    cpd::stored_relations(db)
}

pub open spec fn sr_of(db: Database) -> Seq<Seq<Row>> {
    spd::stored_relations(db)
}

/// The part_sztyidx stored relation of a bound database (the p_type and p_size columns of part).
pub open spec fn xr_of(db: Database) -> Seq<Seq<Row>> {
    sxd::stored_relations(db)
}

/// The suppliers_rank stored relations of a bound database (those of suppliers).
pub open spec fn rr_of(db: Database) -> Seq<Seq<Row>> {
    rkd::stored_relations(db)
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

/// A table whose first constraint is a primary key on column 0: equal keys are one row, and rows are distinct.
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
        db.tables[t].no_duplicates(),
{
    let rows = db.tables[t];
    assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && #[trigger] rows[i][0] == #[trigger] rows[j][0]
        implies i == j by {
        assert(key_of(rows[i], seq![0nat]) =~= key_of(rows[j], seq![0nat]));
        lemma_pk(db, t, seq![0nat], i, j);
    }
    assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && i != j implies rows[i] != rows[j] by {
        if rows[i] == rows[j] {
            assert(rows[i][0] == rows[j][0]);
        }
    }
}

/// The facts of a bound database.
pub proof fn lemma_bound(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        db.tables.len() == 8,
        cpi::represents(sv.custpart, cr_of(db)),
        spi::represents(sv.suppliers, sr_of(db)),
        rows_in_columns(cr_of(db)[1], cpd::stored_columns_t1()),
        rows_in_columns(sr_of(db)[0], spd::stored_columns_t0()),
        rows_in_columns(sr_of(db)[1], spd::stored_columns_t1()),
        rows_in_columns(sr_of(db)[2], spd::stored_columns_t2()),
        rows_in_columns(sr_of(db)[3], spd::stored_columns_t3()),
        tabs_of(db) == (Tabs { p: cr_of(db)[1], s: sr_of(db)[1], ps: sr_of(db)[0], n: sr_of(db)[2], r: sr_of(db)[3] }),
        keys_unique(tabs_of(db)),
        tabs_nodup(tabs_of(db)),
        sxi::represents(sv.part_sztyidx, xr_of(db)),
        xr_of(db)[0].len() == tabs_of(db).p.len(),
        forall|r: int| 0 <= r < tabs_of(db).p.len() ==> #[trigger] xr_of(db)[0][r][0] == tabs_of(db).p[r][4]
            && xr_of(db)[0][r][1] == tabs_of(db).p[r][5],
        sv.suppliers_psrun.len() == ppi::PSRUN_PARTS,
        sv.suppliers_psrun[ppi::RUN as int] is I64,
        ppi::run_ok(ppi::run_i64s(sv.suppliers_psrun[ppi::RUN as int]), tabs_of(db).ps),
        rki::represents(sv.suppliers_rank, rr_of(db)),
        rr_of(db)[0] == tabs_of(db).ps, rr_of(db)[1] == tabs_of(db).s,
{
    assert(ppd::stored_relations(db) =~= spd::stored_relations(db));
    assert(rkd::stored_relations(db) =~= spd::stored_relations(db));
    cpd::lemma_declared_schema();
    spd::lemma_declared_schema();
    cpd::lemma_stored_relations(db);
    spd::lemma_stored_relations(db);
    crate::gendb_constraints::lemma_declared_schema();
    assert(db.tables.len() == 8);
    // Widths of the five tables' rows (db_wf).
    assert forall|t: int, i: int| 3 <= t < 8 && 0 <= i < db.tables[t].len()
        implies (#[trigger] db.tables[t][i]).len() == schema_spec()[t].columns.len() by {
        assert(row_in_table(db.tables[t][i], db.schema[t]));
    }
    lemma_proj_full(db.tables[3], cpd::stored_cols_t1(), 9);
    crate::link::source::lemma_proj_all_index(db.tables[3], sxd::stored_cols_t0());
    lemma_proj_full(db.tables[4], spd::stored_cols_t0(), 5);
    lemma_proj_full(db.tables[5], spd::stored_cols_t1(), 7);
    lemma_proj_full(db.tables[6], spd::stored_cols_t2(), 4);
    lemma_proj_full(db.tables[7], spd::stored_cols_t3(), 3);
    assert(declared_schema()[3].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[4].constraints[0] == (Constraint::Key { cols: seq![0nat, 1nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[5].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[6].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[7].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    lemma_pk0(db, 3);
    lemma_pk0(db, 5);
    lemma_pk0(db, 6);
    lemma_pk0(db, 7);
    let ps = db.tables[4];
    assert forall|i: int, j: int| 0 <= i < ps.len() && 0 <= j < ps.len() && i != j implies ps[i] != ps[j] by {
        if ps[i] == ps[j] {
            assert(key_of(ps[i], seq![0nat, 1nat]) =~= key_of(ps[j], seq![0nat, 1nat]));
            lemma_pk(db, 4, seq![0nat, 1nat], i, j);
        }
    }
}

/// Every database bound to the same parts has the same five tables.
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
