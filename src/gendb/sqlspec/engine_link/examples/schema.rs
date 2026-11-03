//! The schema of the toolkit examples: two NOT NULL tables (positions are what the ASTs address).
//! - table 0, "outer": key int8, day date, qty numeric(15,2)
//! - table 1, "inner": key int8, a date, b date, qty numeric(15,2)
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::typing::*;
use crate::engine_link::classes::*;
use crate::engine_link::classes_values::lemma_table_rows_in;

verus! {

pub open spec fn outer_table() -> TableSchema {
    TableSchema {
        columns: seq![
            Column { ty: SqlType::Int8, nullable: false },
            Column { ty: SqlType::Date, nullable: false },
            Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false },
        ],
        constraints: seq![],
    }
}

pub open spec fn inner_table() -> TableSchema {
    TableSchema {
        columns: seq![
            Column { ty: SqlType::Int8, nullable: false },
            Column { ty: SqlType::Date, nullable: false },
            Column { ty: SqlType::Date, nullable: false },
            Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false },
        ],
        constraints: seq![],
    }
}

pub open spec fn example_schema() -> Schema {
    seq![outer_table(), inner_table()]
}

/// A well-formed database of the example schema.
pub open spec fn example_db(db: Database) -> bool {
    db.schema == example_schema() && db_wf(db)
}

/// The hypothesis is satisfiable: the schema is well-formed and its empty database satisfies `example_db`.
pub proof fn lemma_example_db_exists()
    ensures example_db(Database { schema: example_schema(), tables: seq![Seq::<Row>::empty(), Seq::<Row>::empty()] }),
{
    assert(schema_wf(example_schema())) by (compute);
}

pub open spec fn outer_classes() -> Seq<VClass> {
    table_classes(outer_table())
}

pub open spec fn inner_classes() -> Seq<VClass> {
    table_classes(inner_table())
}

/// The day of a date value (0 otherwise).
pub open spec fn day_of(v: Val) -> int {
    match v {
        Val::Date(d) => d,
        _ => 0,
    }
}

/// Every row of either table lies in its column classes: an int8 key, dates, a numeric of scale 2.
pub proof fn lemma_example_rows(db: Database)
    requires example_db(db),
    ensures
        db.tables.len() == 2,
        rows_in(db.tables[0], outer_classes()),
        rows_in(db.tables[1], inner_classes()),
        forall|i: int| 0 <= i < db.tables[0].len() ==> {
            let r = #[trigger] db.tables[0][i];
            &&& r.len() == 3 && r[0] is Int && r[1] is Date && (r[2] matches Val::Num { scale, .. } && scale == 2)
        },
        forall|i: int| 0 <= i < db.tables[1].len() ==> {
            let r = #[trigger] db.tables[1][i];
            &&& r.len() == 4 && r[0] is Int && r[1] is Date && r[2] is Date && (r[3] matches Val::Num { scale, .. } && scale == 2)
        },
{
    lemma_table_rows_in(db, 0);
    lemma_table_rows_in(db, 1);
    assert forall|i: int| 0 <= i < db.tables[0].len() implies {
        let r = #[trigger] db.tables[0][i];
        &&& r.len() == 3 && r[0] is Int && r[1] is Date && (r[2] matches Val::Num { scale, .. } && scale == 2)
    } by {
        let r = db.tables[0][i];
        assert(row_in(r, outer_classes()));
        assert(in_class(r[0], outer_classes()[0]) && in_class(r[1], outer_classes()[1]) && in_class(r[2], outer_classes()[2]));
    }
    assert forall|i: int| 0 <= i < db.tables[1].len() implies {
        let r = #[trigger] db.tables[1][i];
        &&& r.len() == 4 && r[0] is Int && r[1] is Date && r[2] is Date && (r[3] matches Val::Num { scale, .. } && scale == 2)
    } by {
        let r = db.tables[1][i];
        assert(row_in(r, inner_classes()));
        assert(in_class(r[0], inner_classes()[0]) && in_class(r[1], inner_classes()[1]));
        assert(in_class(r[2], inner_classes()[2]) && in_class(r[3], inner_classes()[3]));
    }
}

} // verus!
