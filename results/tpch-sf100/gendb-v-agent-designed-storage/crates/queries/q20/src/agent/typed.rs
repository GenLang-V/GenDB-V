//! What a database of the schema gives the statement: typed rows of the five tables it reads (lineitem, part,
//! partsupp, supplier, nation: only the columns the statement reads are constrained) and distinct supplier and
//! nation keys from their declared primary keys (`tables_ok`, `lemma_tables_ok`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::datetime::date_valid;
use crate::spec::constraints::{constraints_hold, key_of};
use crate::link::expr::{ival, tval};
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};

verus! {

/// `10^15`: the exclusive bound of a numeric(15, 2) coefficient.
pub open spec fn p15() -> int {
    1_000_000_000_000_000
}

/// A numeric(15, 2) value.
pub open spec fn num2(v: Val) -> bool {
    v == Val::Num { coeff: ival(v), scale: 2 } && -p15() < ival(v) < p15()
}

/// A bigint value.
pub open spec fn is_int(v: Val) -> bool {
    v == Val::Int(ival(v)) && i64::MIN <= ival(v) <= i64::MAX
}

/// A text value.
pub open spec fn is_text(v: Val) -> bool {
    v == Val::Text(tval(v))
}

/// A date value inside PostgreSQL's date range.
pub open spec fn is_date(v: Val) -> bool {
    v == Val::Date(ival(v)) && date_valid(ival(v))
}

/// A typed lineitem row: l_partkey (1), l_suppkey (2), l_quantity (4), l_shipdate (10).
pub open spec fn lrow_ok(l: Row) -> bool {
    &&& l.len() == 16
    &&& is_int(l[1])
    &&& is_int(l[2])
    &&& num2(l[4])
    &&& is_date(l[10])
}

/// A typed part row: p_partkey (0), p_name (1).
pub open spec fn prow_ok(p: Row) -> bool {
    &&& p.len() == 9
    &&& is_int(p[0])
    &&& is_text(p[1])
}

/// A typed partsupp row: ps_partkey (0), ps_suppkey (1), ps_availqty (2).
pub open spec fn psrow_ok(r: Row) -> bool {
    &&& r.len() == 5
    &&& is_int(r[0])
    &&& is_int(r[1])
    &&& is_int(r[2])
}

/// A typed supplier row: s_suppkey (0), s_name (1), s_address (2), s_nationkey (3).
pub open spec fn srow_ok(r: Row) -> bool {
    &&& r.len() == 7
    &&& is_int(r[0])
    &&& is_text(r[1])
    &&& is_text(r[2])
    &&& is_int(r[3])
}

/// A typed nation row: n_nationkey (0), n_name (1).
pub open spec fn nrow_ok(r: Row) -> bool {
    &&& r.len() == 4
    &&& is_int(r[0])
    &&& is_text(r[1])
}

/// Typed rows of the five tables, distinct supplier keys and distinct nation keys.
pub open spec fn tables_ok(db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& forall|i: int| 0 <= i < db.tables[0].len() ==> lrow_ok(#[trigger] db.tables[0][i])
    &&& forall|i: int| 0 <= i < db.tables[3].len() ==> prow_ok(#[trigger] db.tables[3][i])
    &&& forall|i: int| 0 <= i < db.tables[4].len() ==> psrow_ok(#[trigger] db.tables[4][i])
    &&& forall|i: int| 0 <= i < db.tables[5].len() ==> srow_ok(#[trigger] db.tables[5][i])
    &&& forall|i: int| 0 <= i < db.tables[6].len() ==> nrow_ok(#[trigger] db.tables[6][i])
    &&& forall|a: int, b: int| 0 <= a < db.tables[5].len() && 0 <= b < db.tables[5].len() && a != b
            ==> #[trigger] db.tables[5][a][0] != #[trigger] db.tables[5][b][0]
    &&& forall|a: int, b: int| 0 <= a < db.tables[6].len() && 0 <= b < db.tables[6].len() && a != b
            ==> #[trigger] db.tables[6][a][0] != #[trigger] db.tables[6][b][0]
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
        forall|i: int, j: int| 0 <= i < db.tables[t].len() && 0 <= j < db.tables[t].len() && i != j
            ==> #[trigger] db.tables[t][i][0] != #[trigger] db.tables[t][j][0],
{
    crate::gendb_constraints::lemma_declared_schema();
    let rows = db.tables[t];
    let ddb = declared_db(db);
    assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && i != j
        implies #[trigger] rows[i][0] != #[trigger] rows[j][0] by {
        if rows[i][0] == rows[j][0] {
            assert(key_of(rows[i], seq![0nat]) =~= key_of(rows[j], seq![0nat]));
            crate::bridge::equality::lemma_row_not_distinct_refl(key_of(rows[i], seq![0nat]));
            crate::bridge::constraints::lemma_primary_key_identifies(ddb, t, 0, seq![0nat], true, i, j);
        }
    }
}

/// A database of the schema satisfying the declared constraints has typed rows and distinct supplier and nation keys.
pub proof fn lemma_tables_ok(db: Database)
    requires db.schema == schema_spec(), db_wf(db), constraints_hold(declared_db(db)),
    ensures tables_ok(db),
{
    assert(p15() == 1_000_000_000_000_000);
    assert(crate::spec::numeric::pow10(15) == p15()) by (compute);
    let int8 = Column { ty: SqlType::Int8, nullable: false };
    let num = Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false };
    let text = Column { ty: SqlType::Text, nullable: false };
    let date = Column { ty: SqlType::Date, nullable: false };
    assert(schema_spec().len() == 8) by (compute);
    assert(schema_spec()[0].columns.len() == 16) by (compute);
    assert(schema_spec()[0].columns[1] == int8) by (compute);
    assert(schema_spec()[0].columns[2] == int8) by (compute);
    assert(schema_spec()[0].columns[4] == num) by (compute);
    assert(schema_spec()[0].columns[10] == date) by (compute);
    assert(schema_spec()[3].columns.len() == 9) by (compute);
    assert(schema_spec()[3].columns[0] == int8) by (compute);
    assert(schema_spec()[3].columns[1] == text) by (compute);
    assert(schema_spec()[4].columns.len() == 5) by (compute);
    assert(schema_spec()[4].columns[0] == int8) by (compute);
    assert(schema_spec()[4].columns[1] == int8) by (compute);
    assert(schema_spec()[4].columns[2] == int8) by (compute);
    assert(schema_spec()[5].columns.len() == 7) by (compute);
    assert(schema_spec()[5].columns[0] == int8) by (compute);
    assert(schema_spec()[5].columns[1] == text) by (compute);
    assert(schema_spec()[5].columns[2] == text) by (compute);
    assert(schema_spec()[5].columns[3] == int8) by (compute);
    assert(schema_spec()[6].columns.len() == 4) by (compute);
    assert(schema_spec()[6].columns[0] == int8) by (compute);
    assert(schema_spec()[6].columns[1] == text) by (compute);
    assert(db.tables.len() == 8);
    assert forall|i: int| 0 <= i < db.tables[0].len() implies lrow_ok(#[trigger] db.tables[0][i]) by {
        let r = db.tables[0][i];
        assert(row_in_table(r, db.schema[0]));
        assert(value_in_column(r[1], int8));
        assert(value_in_column(r[2], int8));
        assert(value_in_column(r[4], num));
        assert(value_in_column(r[10], date));
    }
    assert forall|i: int| 0 <= i < db.tables[3].len() implies prow_ok(#[trigger] db.tables[3][i]) by {
        let r = db.tables[3][i];
        assert(row_in_table(r, db.schema[3]));
        assert(value_in_column(r[0], int8));
        assert(value_in_column(r[1], text));
    }
    assert forall|i: int| 0 <= i < db.tables[4].len() implies psrow_ok(#[trigger] db.tables[4][i]) by {
        let r = db.tables[4][i];
        assert(row_in_table(r, db.schema[4]));
        assert(value_in_column(r[0], int8));
        assert(value_in_column(r[1], int8));
        assert(value_in_column(r[2], int8));
    }
    assert forall|i: int| 0 <= i < db.tables[5].len() implies srow_ok(#[trigger] db.tables[5][i]) by {
        let r = db.tables[5][i];
        assert(row_in_table(r, db.schema[5]));
        assert(value_in_column(r[0], int8));
        assert(value_in_column(r[1], text));
        assert(value_in_column(r[2], text));
        assert(value_in_column(r[3], int8));
    }
    assert forall|i: int| 0 <= i < db.tables[6].len() implies nrow_ok(#[trigger] db.tables[6][i]) by {
        let r = db.tables[6][i];
        assert(row_in_table(r, db.schema[6]));
        assert(value_in_column(r[0], int8));
        assert(value_in_column(r[1], text));
    }
    crate::gendb_constraints::lemma_declared_schema();
    assert(declared_schema()[5].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(declared_schema()[6].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert forall|i: int| 0 <= i < db.tables[5].len() implies (#[trigger] db.tables[5][i]).len() > 0 by {
        assert(srow_ok(db.tables[5][i]));
    }
    assert forall|i: int| 0 <= i < db.tables[6].len() implies (#[trigger] db.tables[6][i]).len() > 0 by {
        assert(nrow_ok(db.tables[6][i]));
    }
    lemma_pk0(db, 5);
    lemma_pk0(db, 6);
}

} // verus!
