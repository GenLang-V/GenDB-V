//! What a database of the schema gives the statement: typed lineitem rows (`lrow_ok`: l_partkey an integer,
//! l_quantity and l_extendedprice numeric(15, 2)), typed part rows (`prow_ok`: p_partkey an integer, p_brand and
//! p_container texts), and distinct part keys from the declared primary key of part (`tables_ok`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::numeric::*;
use crate::spec::constraints::{constraints_hold, key_of};
use crate::link::expr::{ival, tval};
use crate::link::query::{proj, proj_all};
use crate::link::source::lemma_proj_all_index;
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};
use super::vals::*;

verus! {

/// A numeric(15, 2) value.
pub open spec fn num2(v: Val) -> bool {
    v == Val::Num { coeff: ival(v), scale: 2 } && -p15() < ival(v) < p15()
}

/// A typed lineitem row (16 columns).
pub open spec fn lrow_ok(l: Row) -> bool {
    &&& l.len() == 16
    &&& l[1] == Val::Int(ival(l[1]))
    &&& num2(l[4])
    &&& num2(l[5])
}

/// A typed part row (9 columns).
pub open spec fn prow_ok(p: Row) -> bool {
    &&& p.len() == 9
    &&& p[0] == Val::Int(ival(p[0]))
    &&& i64::MIN <= ival(p[0]) <= i64::MAX
    &&& p[3] == Val::Text(tval(p[3]))
    &&& p[6] == Val::Text(tval(p[6]))
}

/// The lineitem columns the statement reads: l_partkey, l_quantity, l_extendedprice.
pub open spec fn lcols() -> Seq<nat> {
    seq![1nat, 4nat, 5nat]
}

/// The part columns the statement reads: p_partkey, p_brand, p_container.
pub open spec fn pcols() -> Seq<nat> {
    seq![0nat, 3nat, 6nat]
}

/// The lineitem value rows of a database.
pub open spec fn ys_of(db: Database) -> Seq<Row> {
    proj_all(db.tables[0], lcols())
}

/// The part value rows of a database.
pub open spec fn zs_of(db: Database) -> Seq<Row> {
    proj_all(db.tables[3], pcols())
}

/// Typed rows and distinct part keys.
pub open spec fn tables_ok(db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& forall|i: int| 0 <= i < db.tables[0].len() ==> lrow_ok(#[trigger] db.tables[0][i])
    &&& forall|j: int| 0 <= j < db.tables[3].len() ==> prow_ok(#[trigger] db.tables[3][j])
    &&& forall|a: int, b: int| 0 <= a < db.tables[3].len() && 0 <= b < db.tables[3].len() && a != b
            ==> #[trigger] db.tables[3][a][0] != #[trigger] db.tables[3][b][0]
}

pub proof fn lemma_pow10_15()
    ensures pow10(15) == p15(),
{
    assert(pow10(15) == p15()) by (compute);
}

/// A declared primary key on column 0 identifies the row.
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
    crate::gendb_constraints::lemma_declared_schema();
    let rows = db.tables[t];
    let ddb = declared_db(db);
    assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && #[trigger] rows[i][0] == #[trigger] rows[j][0]
        implies i == j by {
        assert(key_of(rows[i], seq![0nat]) =~= key_of(rows[j], seq![0nat]));
        crate::bridge::equality::lemma_row_not_distinct_refl(key_of(rows[i], seq![0nat]));
        crate::bridge::constraints::lemma_primary_key_identifies(ddb, t, 0, seq![0nat], true, i, j);
    }
}

/// A database of the schema satisfying the declared constraints has typed rows and distinct part keys.
pub proof fn lemma_tables_ok(db: Database)
    requires db.schema == schema_spec(), db_wf(db), constraints_hold(declared_db(db)),
    ensures tables_ok(db),
{
    lemma_pow10_15();
    let int8 = Column { ty: SqlType::Int8, nullable: false };
    let num = Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false };
    let text = Column { ty: SqlType::Text, nullable: false };
    assert(schema_spec().len() == 8) by (compute);
    assert(schema_spec()[0].columns.len() == 16) by (compute);
    assert(schema_spec()[0].columns[1] == int8) by (compute);
    assert(schema_spec()[0].columns[4] == num) by (compute);
    assert(schema_spec()[0].columns[5] == num) by (compute);
    assert(schema_spec()[3].columns.len() == 9) by (compute);
    assert(schema_spec()[3].columns[0] == int8) by (compute);
    assert(schema_spec()[3].columns[3] == text) by (compute);
    assert(schema_spec()[3].columns[6] == text) by (compute);
    assert(db.tables.len() == 8);
    assert forall|i: int| 0 <= i < db.tables[0].len() implies lrow_ok(#[trigger] db.tables[0][i]) by {
        let r = db.tables[0][i];
        assert(row_in_table(r, db.schema[0]));
        assert(value_in_column(r[1], int8));
        assert(value_in_column(r[4], num));
        assert(value_in_column(r[5], num));
    }
    assert forall|j: int| 0 <= j < db.tables[3].len() implies prow_ok(#[trigger] db.tables[3][j]) by {
        let r = db.tables[3][j];
        assert(row_in_table(r, db.schema[3]));
        assert(value_in_column(r[0], int8));
        assert(crate::spec::int::int_in_range(crate::spec::int::IntKind::Int8, ival(r[0])));
        assert(value_in_column(r[3], text));
        assert(value_in_column(r[6], text));
    }
    crate::gendb_constraints::lemma_declared_schema();
    assert(declared_schema()[3].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert forall|i: int| 0 <= i < db.tables[3].len() implies (#[trigger] db.tables[3][i]).len() > 0 by {
        assert(prow_ok(db.tables[3][i]));
    }
    lemma_pk0(db, 3);
}

/// The value rows of typed tables: typed lineitem value rows, part value rows with distinct keys.
pub proof fn lemma_value_rows(db: Database)
    requires tables_ok(db),
    ensures
        ys_ok(ys_of(db)),
        ys_of(db).len() == db.tables[0].len(),
        zs_of(db).len() == db.tables[3].len(),
        keys_distinct(zs_of(db)),
        forall|i: int| 0 <= i < db.tables[0].len() ==> #[trigger] ys_of(db)[i] == proj(db.tables[0][i], lcols()),
        forall|j: int| 0 <= j < db.tables[3].len() ==> #[trigger] zs_of(db)[j] == proj(db.tables[3][j], pcols()),
{
    let (l, p) = (db.tables[0], db.tables[3]);
    lemma_proj_all_index(l, lcols());
    lemma_proj_all_index(p, pcols());
    assert forall|i: int| 0 <= i < ys_of(db).len() implies y_ok(#[trigger] ys_of(db)[i]) by {
        let y = ys_of(db)[i];
        assert(lrow_ok(l[i]));
        assert(y[0] == l[i][1] && y[1] == l[i][4] && y[2] == l[i][5]);
        assert(y =~= yrow(ival(y[0]), ival(y[1]), ival(y[2])));
    }
    assert forall|a: int, b: int| 0 <= a < zs_of(db).len() && 0 <= b < zs_of(db).len() && a != b
        implies #[trigger] zs_of(db)[a][0] != #[trigger] zs_of(db)[b][0] by {
        assert(zs_of(db)[a][0] == p[a][0]);
        assert(zs_of(db)[b][0] == p[b][0]);
    }
}

} // verus!
