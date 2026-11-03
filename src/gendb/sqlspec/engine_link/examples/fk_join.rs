//! Examples: what a foreign key onto a primary key gives a join plan (L7).
//!
//! Schema (positions are what the ASTs address), every column int8 NOT NULL:
//! - table 0, "parent": key, val; PRIMARY KEY (key);
//! - table 1, "child": id, fk; FOREIGN KEY (fk) REFERENCES parent (key).
//!
//! `fk_db(db)`: a well-formed database of this schema whose declared constraints hold (in an engine crate: the
//! declared database `declared_db(db)` of the claim). Two planner rules on `child, parent WHERE child.fk = parent.key`:
//! - `example_fk_join_elim`: `SELECT child.*` of that join is the child rows themselves, in order (join elimination:
//!   every child row has exactly one parent);
//! - `example_pk_array_join`: when the parent keys are dense (a checked storage flag: parent row `l` has key
//!   `base + l`), the join is one array lookup per child row (a primary-key probe without a hash table).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::typing::*;
use crate::spec::constraints::*;
use crate::link::query::{col_exprs, select, lemma_project_cols};
use crate::engine_link::ops::*;
use crate::engine_link::colmap::*;
use crate::engine_link::joins::*;
use crate::engine_link::keys::*;

verus! {

pub open spec fn int8_column() -> Column {
    Column { ty: SqlType::Int8, nullable: false }
}

pub open spec fn parent_table() -> TableSchema {
    TableSchema {
        columns: seq![int8_column(), int8_column()],
        constraints: seq![Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }],
    }
}

pub open spec fn child_table() -> TableSchema {
    TableSchema {
        columns: seq![int8_column(), int8_column()],
        constraints: seq![Constraint::ForeignKey { cols: seq![1nat], table: 0, ref_cols: seq![0nat], match_full: false }],
    }
}

pub open spec fn fk_schema() -> Schema {
    seq![parent_table(), child_table()]
}

/// A well-formed database of the schema whose declared constraints hold.
pub open spec fn fk_db(db: Database) -> bool {
    db.schema == fk_schema() && db_wf(db) && constraints_hold(db)
}

/// The hypothesis is satisfiable: the schema is well-formed and the empty database of it satisfies `fk_db`.
pub proof fn lemma_fk_db_exists()
    ensures fk_db(Database { schema: fk_schema(), tables: seq![Seq::<Row>::empty(), Seq::<Row>::empty()] }),
{
    assert(schema_wf(fk_schema())) by (compute);
    let db = Database { schema: fk_schema(), tables: seq![Seq::<Row>::empty(), Seq::<Row>::empty()] };
    assert(constraints_hold(db)) by {
        assert forall|t: int, k: int| 0 <= t < db.schema.len() && t < db.tables.len() && 0 <= k < db.schema[t].constraints.len()
            implies constraint_holds(db, t, #[trigger] db.schema[t].constraints[k]) by {
            assert(db.tables[t].len() == 0);
        }
    }
}

/// Every row of either table is two integers.
pub proof fn lemma_fk_rows(db: Database)
    requires fk_db(db),
    ensures
        db.tables.len() == 2,
        width_of(db.tables[0], 2),
        width_of(db.tables[1], 2),
        forall|i: int| 0 <= i < db.tables[0].len() ==> (#[trigger] db.tables[0][i])[0] is Int && db.tables[0][i][1] is Int,
        forall|i: int| 0 <= i < db.tables[1].len() ==> (#[trigger] db.tables[1][i])[0] is Int && db.tables[1][i][1] is Int,
{
    assert forall|t: int, i: int| 0 <= t < 2 && 0 <= i < db.tables[t].len() implies
        (#[trigger] db.tables[t][i]).len() == 2 && db.tables[t][i][0] is Int && db.tables[t][i][1] is Int by {
        let r = db.tables[t][i];
        assert(row_in_table(r, db.schema[t]));
        assert(db.schema[t].columns == seq![int8_column(), int8_column()]);
        assert(value_in_column(r[0], int8_column()) && value_in_column(r[1], int8_column()));
    }
    assert forall|i: int| 0 <= i < db.tables[0].len() implies (#[trigger] db.tables[0][i])[0] is Int && db.tables[0][i][1] is Int by {
        assert(db.tables[0][i].len() == 2);
    }
    assert forall|i: int| 0 <= i < db.tables[1].len() implies (#[trigger] db.tables[1][i])[0] is Int && db.tables[1][i][1] is Int by {
        assert(db.tables[1][i].len() == 2);
    }
}

/// `child, parent WHERE child.fk = parent.key` (joined rows: id, fk, key, val).
pub open spec fn fk_join_query() -> Query {
    Query::Filter {
        pred: equi_pred(0, 2, 1, 0),
        input: Box::new(Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) }),
    }
}

/// `SELECT child.id, child.fk` of the join.
pub open spec fn fk_elim_query() -> Query {
    Query::Project { exprs: col_exprs(seq![0nat, 1nat]), input: Box::new(fk_join_query()) }
}

/// The parent of a child row: the one row of its bucket.
pub open spec fn parent_of(parent: Seq<Row>) -> spec_fn(Row) -> Row {
    |x: Row| eq_bucket(parent, 0, x[1])[0]
}

/// The join is the hash join, and every child row's bucket is exactly its parent (the foreign key onto the primary
/// key).
pub proof fn lemma_fk_join(db: Database)
    requires fk_db(db),
    ensures
        eval_query(db, Seq::empty(), fk_join_query()) == Ok::<Relation, SqlError>(equi_join(db.tables[1], db.tables[0], 1, 0)),
        forall|k: int| 0 <= k < db.tables[1].len() ==>
            #[trigger] eq_bucket(db.tables[0], 0, db.tables[1][k][1]) == seq![parent_of(db.tables[0])(db.tables[1][k])],
        forall|k: int| 0 <= k < db.tables[1].len() ==> (#[trigger] parent_of(db.tables[0])(db.tables[1][k])).len() == 2,
{
    hide(eval_query);
    lemma_fk_rows(db);
    let (parent, child) = (db.tables[0], db.tables[1]);
    let ctx = Seq::<Val>::empty();
    assert(keys_comparable(child, parent, 1, 0)) by {
        assert forall|k: int, l: int| 0 <= k < child.len() && 0 <= l < parent.len() implies
            #[trigger] child[k][1] is Null || #[trigger] parent[l][0] is Null || compare(child[k][1], parent[l][0]) is Some by {
            assert(child[k][1] is Int && parent[l][0] is Int);
        }
    }
    assert(has_col(parent, 0));
    lemma_equi_join(db, ctx, child, parent, 2, 1, 0);
    lemma_eval_op(db, ctx, fk_join_query());
    lemma_eval_op(db, ctx, Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) });
    lemma_eval_op(db, ctx, Query::Table(0));
    lemma_eval_op(db, ctx, Query::Table(1));
    assert(fk_at(db, 1, 0, seq![1nat], 0, seq![0nat], false, 0, true, true));
    assert forall|k: int| 0 <= k < child.len() implies
        #[trigger] eq_bucket(parent, 0, child[k][1]) == seq![parent_of(parent)(child[k])]
        && parent_of(parent)(child[k]).len() == 2 by {
        let j = lemma_fk_bucket(db, 1, 0, 1, 0, 0, false, 0, true, true, k);
        assert(parent[j].len() == 2);
    }
}

/// L7 join elimination: `SELECT child.* FROM child, parent WHERE child.fk = parent.key` is the child table, in order.
pub proof fn example_fk_join_elim(db: Database)
    requires fk_db(db),
    ensures eval_query(db, Seq::empty(), fk_elim_query()) == Ok::<Relation, SqlError>(db.tables[1]),
{
    lemma_fk_rows(db);
    lemma_fk_join(db);
    let (parent, child) = (db.tables[0], db.tables[1]);
    let joined = equi_join(child, parent, 1, 0);
    let outs = seq![0nat, 1nat];
    lemma_one_match_join(child, parent, 1, 0, parent_of(parent));
    lemma_join_elim(child, parent, 1, 0, 2, parent_of(parent));
    assert(width_of(joined, 4)) by {
        assert forall|k: int| 0 <= k < joined.len() implies (#[trigger] joined[k]).len() == 4 by {
            assert(joined[k] == child[k] + parent_of(parent)(child[k]));
        }
    }
    lemma_project_cols(db, fk_join_query(), joined, outs, 4);
    let selected = joined.map_values(|r: Row| select(r, outs));
    assert(selected =~= child) by {
        assert forall|k: int| 0 <= k < child.len() implies #[trigger] selected[k] == child[k] by {
            assert(select(joined[k], outs) =~= map_row(id_map(2), joined[k]));
            assert(map_rows(id_map(2), joined)[k] == child[k]);
        }
    }
}

/// L7 array join: with dense parent keys, `SELECT * FROM child, parent WHERE child.fk = parent.key` is every child row
/// followed by the parent row at offset `fk - base`.
pub proof fn example_pk_array_join(db: Database, base: int)
    requires fk_db(db), dense_on(db.tables[0], 0, base),
    ensures
        eval_query(db, Seq::empty(), fk_join_query())
            == Ok::<Relation, SqlError>(db.tables[1].map_values(with_partner(dense_partner(db.tables[0], 1, base)))),
{
    lemma_fk_rows(db);
    lemma_fk_join(db);
    let (parent, child) = (db.tables[0], db.tables[1]);
    // the foreign key puts every child key inside the dense range
    assert forall|k: int| 0 <= k < child.len() implies
        (#[trigger] child[k][1]) is Int && 0 <= int_of(child[k][1]) - base < parent.len() by {
        let v = int_of(child[k][1]);
        assert(child[k][1] == Val::Int(v));
        lemma_dense_bucket(parent, 0, base, v);
        assert(eq_bucket(parent, 0, child[k][1]).len() == 1);
    }
    lemma_array_join(child, parent, 1, 0, base);
}

} // verus!
