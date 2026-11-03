// Framework test fixture (integrity constraints, T3; hand-written framework test input, not an author output): appended
// to the `verus_storage` builder in a storage crate of the storage entry v2 (the manifest opts in with
// `uses_declared_constraints`) whose run declares `PRIMARY KEY (id)` on sensor. The lemma reads the entry's
// precondition `source_witnessed` through a chosen full witness database and SQLSpec's bridge lemma, and transfers the
// key to the delivered rows by row position: two different delivered rows of sensor have different ids. The builder
// variant requires `source_witnessed(src@)` (the entry provides it) and uses the lemma; without the entry's
// precondition the builder's call does not verify.
use crate::gendb_constraints::{declared_db, declared_schema, lemma_declared_schema};
use crate::gendb_entry::source_witnessed;
use crate::schema::schema_spec;
use crate::spec::constraints::{constraints_hold, key_of};
use crate::spec::equality::row_not_distinct;
use crate::spec::typing::db_wf;
use crate::spec::types::Constraint;
use crate::bridge::constraints::lemma_primary_key_identifies;
use crate::link::source::lemma_proj_all_index;

verus! {

/// Two different delivered rows of sensor (`table_t0(v)`, id first) carry different ids: the declared PRIMARY KEY (id)
/// is sensor's constraint 0 of the declared schema and holds on the full witness database, whose sensor rows the
/// delivered rows are, position by position (the source binding: sensor's columns id, reading, day).
pub proof fn lemma_delivered_ids_distinct(v: SourceView, i: int, j: int)
    requires
        source_witnessed(v),
        0 <= i < table_t0(v).len(),
        0 <= j < table_t0(v).len(),
        i != j,
    ensures
        table_t0(v)[i][0] != table_t0(v)[j][0],
{
    let db = choose|db: Database|
        db.schema == schema_spec() && db_wf(db) && constraints_hold(declared_db(db)) && #[trigger] source_columns_are_tables(v, db);
    lemma_declared_schema();
    let d = declared_db(db);
    assert(declared_schema().len() == 2 && declared_schema()[1].constraints.len() == 1
        && declared_schema()[1].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true })) by (compute);
    assert(source_table_t0() == 1 && source_cols_t0() == seq![0nat, 2, 3]);
    lemma_proj_all_index(db.tables[1], source_cols_t0());
    assert(table_t0(v)[i][0] == db.tables[1][i][0] && table_t0(v)[j][0] == db.tables[1][j][0]);
    if table_t0(v)[i][0] == table_t0(v)[j][0] {
        let (ki, kj) = (key_of(d.tables[1][i], seq![0nat]), key_of(d.tables[1][j], seq![0nat]));
        assert(ki.len() == 1 && ki[0] == table_t0(v)[i][0] && kj.len() == 1 && kj[0] == table_t0(v)[j][0]);
        assert(ki[0] == Val::Int(v.t0_f0[i] as int));
        assert(row_not_distinct(ki, kj));
        lemma_primary_key_identifies(d, 1, 0, seq![0nat], true, i, j);
    }
}

} // verus!
