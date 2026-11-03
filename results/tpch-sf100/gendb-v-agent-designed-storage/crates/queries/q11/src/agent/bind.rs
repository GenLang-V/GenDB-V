//! What a database bound to the stored parts (`gendb_entry::bound_db`) gives the plan: its partsupp, supplier and
//! nation tables are the stored relations of `suppliers` (every column is stored, in canonical order), the parts
//! determine them (every bound database has the same three tables, `lemma_bound_same`), their values have the
//! declared types (`tabs_typed`) and the declared primary keys of supplier and nation are unique (`keys_unique`);
//! the use `suppliers_psrun` (the same relations) adds the run layout of partsupp's ps_partkey (`ppi::run_ok`); the use
//! `ps_suppidx` indexes partsupp's ps_suppkey column (`bitmap::supp_rel`).
//! (Adapted from an admitted Q2 module.)
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::{Constraint, Column, SqlType};
use crate::spec::constraints::{constraints_hold, key_of};
use crate::spec::typing::{db_wf, row_in_table, value_in_column};
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::{proj, proj_all};
use crate::link::source::rows_in_columns;
use crate::stores::suppliers::interface as spi;
use crate::stores::suppliers::declaration as spd;
use crate::stores::suppliers_psrun::interface as ppi;
use crate::stores::suppliers_psrun::declaration as ppd;
use crate::stores::ps_suppidx::interface as six;
use crate::stores::ps_suppidx::declaration as sid;
use super::bitmap::supp_rel;
use super::tables::Tabs;
use super::nf::{keys_unique, tabs_typed, ps_typed, s_typed, n_typed};

verus! {

/// The three tables of the statement in a database: partsupp (4), supplier (5), nation (6).
pub open spec fn tabs_of(db: Database) -> Tabs {
    Tabs { ps: db.tables[4], s: db.tables[5], n: db.tables[6] }
}

/// The suppliers stored relations of a database.
pub open spec fn sr_of(db: Database) -> Seq<Seq<Row>> {
    spd::stored_relations(db)
}

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

/// Values of the declared column types: the typing facts the normal form uses.
proof fn lemma_typed(t: Tabs)
    requires
        rows_in_columns(t.ps, spd::stored_columns_t0()),
        rows_in_columns(t.s, spd::stored_columns_t1()),
        rows_in_columns(t.n, spd::stored_columns_t2()),
    ensures tabs_typed(t),
{
    let c0 = spd::stored_columns_t0();
    let c1 = spd::stored_columns_t1();
    let c2 = spd::stored_columns_t2();
    assert forall|k: int| 0 <= k < t.ps.len() implies #[trigger] ps_typed(t.ps[k]) by {
        let r = t.ps[k];
        assert(r.len() == c0.len());
        assert(value_in_column(r[0], c0[0]));
        assert(value_in_column(r[1], c0[1]));
        assert(value_in_column(r[2], c0[2]));
        assert(value_in_column(r[3], c0[3]));
    }
    assert forall|j: int| 0 <= j < t.s.len() implies #[trigger] s_typed(t.s[j]) by {
        let r = t.s[j];
        assert(r.len() == c1.len());
        assert(value_in_column(r[0], c1[0]));
        assert(value_in_column(r[3], c1[3]));
    }
    assert forall|q: int| 0 <= q < t.n.len() implies #[trigger] n_typed(t.n[q]) by {
        let r = t.n[q];
        assert(r.len() == c2.len());
        assert(value_in_column(r[0], c2[0]));
        assert(value_in_column(r[1], c2[1]));
    }
}

/// The facts of a bound database.
pub proof fn lemma_bound(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        db.tables.len() == 8,
        spi::represents(sv.suppliers, sr_of(db)),
        rows_in_columns(sr_of(db)[0], spd::stored_columns_t0()),
        rows_in_columns(sr_of(db)[1], spd::stored_columns_t1()),
        rows_in_columns(sr_of(db)[2], spd::stored_columns_t2()),
        tabs_of(db) == (Tabs { ps: sr_of(db)[0], s: sr_of(db)[1], n: sr_of(db)[2] }),
        keys_unique(tabs_of(db)),
        tabs_typed(tabs_of(db)),
        sv.suppliers_psrun.len() == ppi::PSRUN_PARTS,
        sv.suppliers_psrun[ppi::RUN as int] is I64,
        ppi::run_ok(ppi::run_i64s(sv.suppliers_psrun[ppi::RUN as int]), tabs_of(db).ps),
        six::represents(sv.ps_suppidx, sid::stored_relations(db)),
        sid::stored_relations(db)[0] == supp_rel(tabs_of(db)),
{
    // Both uses store the same relations (suppliers_psrun extends suppliers).
    assert(ppd::stored_relations(db) =~= spd::stored_relations(db));
    spd::lemma_declared_schema();
    spd::lemma_stored_relations(db);
    crate::gendb_constraints::lemma_declared_schema();
    assert(db.tables.len() == 8);
    // Widths of the three tables' rows (db_wf).
    assert forall|t: int, i: int| 4 <= t < 7 && 0 <= i < db.tables[t].len()
        implies (#[trigger] db.tables[t][i]).len() == schema_spec()[t].columns.len() by {
        assert(row_in_table(db.tables[t][i], db.schema[t]));
    }
    lemma_proj_full(db.tables[4], spd::stored_cols_t0(), 5);
    lemma_proj_full(db.tables[5], spd::stored_cols_t1(), 7);
    lemma_proj_full(db.tables[6], spd::stored_cols_t2(), 4);
    assert(declared_schema()[5].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[6].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    lemma_pk0(db, 5);
    lemma_pk0(db, 6);
    lemma_typed(tabs_of(db));
    // The index's relation is the ps_suppkey column of partsupp.
    let ps = db.tables[4];
    crate::link::source::lemma_proj_all_index(ps, sid::stored_cols_t0());
    assert(sid::stored_cols_t0() =~= seq![1nat]);
    assert forall|r: int| 0 <= r < ps.len() implies #[trigger] sid::stored_relations(db)[0][r] == supp_rel(tabs_of(db))[r] by {
        assert(sid::stored_relations(db)[0][r] =~= seq![ps[r][1]]);
    }
    assert(sid::stored_relations(db)[0] =~= supp_rel(tabs_of(db)));
}

/// Every database bound to the same parts has the same three tables.
pub proof fn lemma_bound_same(sv: StoresView, db1: Database, db2: Database)
    requires bound_db(sv, db1), bound_db(sv, db2),
    ensures tabs_of(db1) == tabs_of(db2),
{
    lemma_bound(sv, db1);
    lemma_bound(sv, db2);
    spi::lemma_represents_determines(sv.suppliers, sr_of(db1), sr_of(db2));
}

} // verus!
