//! What a well-formed database of the schema gives the statement: the four tables' row widths and the types of the
//! columns Q21 reads (supplier: s_suppkey, s_name, s_nationkey; lineitem: l_orderkey, l_suppkey, l_commitdate,
//! l_receiptdate; orders: o_orderkey, o_orderstatus; nation: n_nationkey, n_name), from the declared schema
//! (`stores::*::declaration::lemma_declared_schema`) and `db_wf`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::typing::*;
use crate::spec::types::*;
use crate::schema::schema_spec;
use super::bind::db_ok;
use super::sqlrow::lrow_typed;

verus! {

/// A supplier row: 7 columns, s_suppkey and s_nationkey integers, s_name a text.
pub open spec fn srow_typed(r: Row) -> bool {
    r.len() == 7 && r[0] is Int && r[1] is Text && r[3] is Int
}

/// An orders row: 9 columns, o_orderkey an integer, o_orderstatus a text.
pub open spec fn orow_typed(r: Row) -> bool {
    r.len() == 9 && r[0] is Int && r[2] is Text
}

/// A nation row: 4 columns, n_nationkey an integer, n_name a text.
pub open spec fn nrow_typed(r: Row) -> bool {
    r.len() == 4 && r[0] is Int && r[1] is Text
}

/// Every row of the four tables is typed.
pub open spec fn tables_typed(db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& forall|i: int| 0 <= i < db.tables[5].len() ==> #[trigger] srow_typed(db.tables[5][i])
    &&& forall|i: int| 0 <= i < db.tables[0].len() ==> #[trigger] lrow_typed(db.tables[0][i])
    &&& forall|i: int| 0 <= i < db.tables[1].len() ==> #[trigger] orow_typed(db.tables[1][i])
    &&& forall|i: int| 0 <= i < db.tables[6].len() ==> #[trigger] nrow_typed(db.tables[6][i])
}

pub proof fn lemma_tables_typed(db: Database)
    requires db_ok(db),
    ensures tables_typed(db),
{
    crate::stores::facts::declaration::lemma_declared_schema();
    crate::stores::suppliers::declaration::lemma_declared_schema();
    let s = schema_spec();
    let i8 = Column { ty: SqlType::Int8, nullable: false };
    let tx = Column { ty: SqlType::Text, nullable: false };
    let dt = Column { ty: SqlType::Date, nullable: false };
    // supplier
    let (c5, s5) = (crate::stores::suppliers::declaration::stored_cols_t1(), crate::stores::suppliers::declaration::stored_columns_t1());
    assert(s[5].columns[0] == s5[0] && s[5].columns[1] == s5[1] && s[5].columns[3] == s5[3]) by {
        assert(c5[0] == 0 && c5[1] == 1 && c5[3] == 3);
    }
    assert(s5[0] == i8 && s5[1] == tx && s5[3] == i8);
    // nation
    let (c6, s6) = (crate::stores::suppliers::declaration::stored_cols_t2(), crate::stores::suppliers::declaration::stored_columns_t2());
    assert(s[6].columns[0] == s6[0] && s[6].columns[1] == s6[1]) by {
        assert(c6[0] == 0 && c6[1] == 1);
    }
    assert(s6[0] == i8 && s6[1] == tx);
    // lineitem
    let (c0, s0) = (crate::stores::facts::declaration::stored_cols_t0(), crate::stores::facts::declaration::stored_columns_t0());
    assert(s[0].columns[0] == s0[0] && s[0].columns[2] == s0[2] && s[0].columns[11] == s0[11] && s[0].columns[12] == s0[12]) by {
        assert(c0[0] == 0 && c0[2] == 2 && c0[11] == 11 && c0[12] == 12);
    }
    assert(s0[0] == i8 && s0[2] == i8 && s0[11] == dt && s0[12] == dt);
    // orders
    let (c1, s1) = (crate::stores::facts::declaration::stored_cols_t1(), crate::stores::facts::declaration::stored_columns_t1());
    assert(s[1].columns[0] == s1[0] && s[1].columns[2] == s1[2]) by {
        assert(c1[0] == 0 && c1[2] == 2);
    }
    assert(s1[0] == i8 && s1[2] == tx);
    assert forall|i: int| 0 <= i < db.tables[5].len() implies #[trigger] srow_typed(db.tables[5][i]) by {
        let r = db.tables[5][i];
        assert(row_in_table(r, db.schema[5]));
        assert(value_in_column(r[0], s[5].columns[0]));
        assert(value_in_column(r[1], s[5].columns[1]));
        assert(value_in_column(r[3], s[5].columns[3]));
    }
    assert forall|i: int| 0 <= i < db.tables[0].len() implies #[trigger] lrow_typed(db.tables[0][i]) by {
        let r = db.tables[0][i];
        assert(row_in_table(r, db.schema[0]));
        assert(value_in_column(r[0], s[0].columns[0]));
        assert(value_in_column(r[2], s[0].columns[2]));
        assert(value_in_column(r[11], s[0].columns[11]));
        assert(value_in_column(r[12], s[0].columns[12]));
    }
    assert forall|i: int| 0 <= i < db.tables[1].len() implies #[trigger] orow_typed(db.tables[1][i]) by {
        let r = db.tables[1][i];
        assert(row_in_table(r, db.schema[1]));
        assert(value_in_column(r[0], s[1].columns[0]));
        assert(value_in_column(r[2], s[1].columns[2]));
    }
    assert forall|i: int| 0 <= i < db.tables[6].len() implies #[trigger] nrow_typed(db.tables[6][i]) by {
        let r = db.tables[6][i];
        assert(row_in_table(r, db.schema[6]));
        assert(value_in_column(r[0], s[6].columns[0]));
        assert(value_in_column(r[1], s[6].columns[1]));
    }
}

} // verus!
