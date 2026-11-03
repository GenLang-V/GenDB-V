//! Facts of every database bound to the stored parts (`gendb_entry::bound_db`): the storages' layouts, and the
//! declared primary key of `sub` (`adsh`) as a fact of the parts (`fspec::adsh_unique`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::equality::*;
use crate::spec::constraints::{constraints_hold, key_of};
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::stores::num::interface as ni;
use crate::stores::pre::interface as pi;
use crate::stores::sub::interface as si;
use crate::agent::views::*;
use crate::agent::fspec::*;

verus! {

/// A bound database gives the views' base facts.
pub proof fn lemma_bound_base(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures base(sv, db), layouts(sv),
{
}

/// The declared primary key of `sub` is `(adsh)`.
proof fn lemma_sub_pk_decl()
    ensures
        declared_schema().len() == 4,
        declared_schema()[0].constraints.len() == 1,
        declared_schema()[0].constraints[0] == (crate::spec::types::Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }),
{
    assert(declared_schema().len() == 4) by (compute);
    assert(declared_schema()[0].constraints.len() == 1) by (compute);
    assert(declared_schema()[0].constraints[0] == (crate::spec::types::Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true })) by (compute);
}

/// Two `sub` rows with the same adsh are the same row.
proof fn lemma_pk_pair(sv: StoresView, db: Database, j1: int, j2: int)
    requires bound_db(sv, db), 0 <= j1 < s_count(sv), 0 <= j2 < s_count(sv), s_adsh(sv, j1) == s_adsh(sv, j2),
    ensures j1 == j2,
{
    lemma_sub_row(sv, db, j1);
    lemma_sub_row(sv, db, j2);
    lemma_sub_pk_decl();
    let ddb = declared_db(db);
    let cols = seq![0nat];
    let (k1, k2) = (key_of(db.tables[0][j1], cols), key_of(db.tables[0][j2], cols));
    assert(k1 =~= seq![db.tables[0][j1][0]]);
    assert(k2 =~= seq![db.tables[0][j2][0]]);
    lemma_lex_cmp_zero(s_adsh(sv, j1), s_adsh(sv, j2));
    assert(val_not_distinct(k1[0], k2[0]));
    assert(row_not_distinct(k1, k2));
    lemma_stored_tables(db);
    assert(ddb.tables == db.tables);
    assert(ddb.schema == declared_schema());
    assert(constraints_hold(ddb));
    lemma_primary_key_identifies(ddb, 0, 0, cols, true, j1, j2);
}

/// The parts of every bound database satisfy the layouts and the `sub` primary key.
pub proof fn lemma_bound_facts(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures layouts(sv), adsh_unique(sv),
{
    assert forall|j1: int, j2: int| 0 <= j1 < s_count(sv) && 0 <= j2 < s_count(sv) && #[trigger] s_adsh(sv, j1) == #[trigger] s_adsh(sv, j2)
        implies j1 == j2 by {
        lemma_pk_pair(sv, db, j1, j2);
    }
}

} // verus!
