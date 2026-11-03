//! Facts every database bound to the stored parts satisfies: its table `pre` is the rows the `pre` parts hold
//! (`lemma_pre_table`), and distinct `sub` rows hold distinct adsh values (the declared primary key of `sub`,
//! `lemma_sub_distinct`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::equality::*;
use crate::spec::constraints::constraints_hold;
use crate::spec::types::Constraint;
use crate::spec::typing::db_wf;
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::gendb_entry::{bound_db};
use crate::gendb_entry::stores::{StoresView, stored_ok};
use crate::bridge::equality::lemma_val_not_distinct_structural;
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::link::query::{proj, proj_all};
use crate::link::source::lemma_proj_all_index;
use crate::stores::flat_pre::declaration as pre_decl;
use crate::stores::flat_sub::declaration as sub_decl;
use crate::agent::cols::*;
use crate::agent::sql::{c10, rows10, lemma_proj_all_id};
use crate::agent::distinct::sub_distinct;

verus! {

/// The table `pre` of a bound database is the rows its parts hold.
pub proof fn lemma_pre_table(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures 3 < db.tables.len(), db.tables[3] == pre_rows(sv.flat_pre),
{
    pre_decl::lemma_declared_schema();
    let rels = pre_decl::stored_relations(db);
    lemma_pre_rows(sv.flat_pre, rels);
    let t = db.tables[3];
    assert forall|i: int| 0 <= i < t.len() implies (#[trigger] t[i]).len() == 10 by {
        assert(crate::spec::typing::row_in_table(db.tables[3][i], db.schema[3]));
    }
    assert(pre_decl::stored_cols_t0() =~= c10());
    lemma_proj_all_id(t);
}

/// Distinct `sub` rows hold distinct adsh values.
pub proof fn lemma_sub_distinct(c: Cols, sv: StoresView, db: Database)
    requires bound_db(sv, db), sub_corr(c, sub_rows(sv.flat_sub)),
    ensures sub_distinct(c),
{
    sub_decl::lemma_declared_schema();
    crate::gendb_constraints::lemma_declared_schema();
    let rels = sub_decl::stored_relations(db);
    lemma_sub_rows(sv.flat_sub, rels);
    let s = sub_rows(sv.flat_sub);
    let ddb = declared_db(db);
    let t0 = db.tables[0];
    lemma_proj_all_index(t0, sub_decl::stored_cols_t0());
    assert(declared_schema()[0].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert forall|j1: int, j2: int| 0 <= j1 < c.m && 0 <= j2 < c.m && j1 != j2
        implies #[trigger] c.subtext(j1) != #[trigger] c.subtext(j2) by {
        if c.subtext(j1) == c.subtext(j2) {
            assert(s[j1][0] == Val::Text(c.subtext(j1)));
            assert(s[j2][0] == Val::Text(c.subtext(j2)));
            assert(s[j1] == proj(t0[j1], sub_decl::stored_cols_t0()));
            assert(s[j2] == proj(t0[j2], sub_decl::stored_cols_t0()));
            assert(t0[j1][0] == s[j1][0]);
            assert(t0[j2][0] == s[j2][0]);
            let k1 = crate::spec::constraints::key_of(t0[j1], seq![0nat]);
            let k2 = crate::spec::constraints::key_of(t0[j2], seq![0nat]);
            assert(k1 =~= seq![t0[j1][0]]);
            assert(k2 =~= seq![t0[j2][0]]);
            lemma_val_not_distinct_structural(k1[0], k2[0]);
            assert(row_not_distinct(k1, k2));
            lemma_primary_key_identifies(ddb, 0, 0, seq![0nat], true, j1, j2);
        }
    }
}

} // verus!
