
// Framework test fixture (integrity constraints, T2; hand-written framework test input, not an author output): appended
// to the `verus_storage` query module in a crate whose request declares `PRIMARY KEY (id)` on sensor, so the crate uses
// the query entry v5. The lemma reads the entry's constraint hypothesis through `declared_db` and SQLSpec's bridge
// lemma: in every database bound to the stored parts, two different rows of sensor have SQL-distinct ids. Without the
// declared key, or without the entry's `constraints_hold(declared_db(db))` conjunct, it does not verify.
use crate::gendb_constraints::{declared_db, declared_schema, lemma_declared_schema};
use crate::spec::constraints::key_of;
use crate::spec::equality::row_not_distinct;
use crate::spec::types::Constraint;
use crate::bridge::constraints::lemma_primary_key_identifies;

verus! {

/// Two different rows of sensor (table 1) of a database bound to the stored parts have distinct `id` tuples: the
/// declared PRIMARY KEY (id) is sensor's constraint 0 of the declared schema.
pub proof fn lemma_declared_key_distinct(sv: StoresView, db: Database, i: int, j: int)
    requires
        bound_db(sv, db),
        0 <= i < db.tables[1].len(),
        0 <= j < db.tables[1].len(),
        i != j,
    ensures
        !row_not_distinct(key_of(db.tables[1][i], seq![0nat]), key_of(db.tables[1][j], seq![0nat])),
{
    lemma_declared_schema();
    let d = declared_db(db);
    assert(declared_schema().len() == 2 && declared_schema()[1].constraints.len() == 1
        && declared_schema()[1].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true })) by (compute);
    if row_not_distinct(key_of(d.tables[1][i], seq![0nat]), key_of(d.tables[1][j], seq![0nat])) {
        lemma_primary_key_identifies(d, 1, 0, seq![0nat], true, i, j);
    }
}

} // verus!
