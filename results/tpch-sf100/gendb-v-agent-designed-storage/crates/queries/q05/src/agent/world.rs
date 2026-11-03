//! The database behind the stored parts: for every database bound to the storage uses, the stored relations
//! the query reads (`rels_of_db`) are the ones the parts represent (`lemma_storage_rels`), the same for every bound
//! database (`lemma_rels_determined`), with the column shapes of the schema (`rels_shapes`) and unique keys on the
//! dimension tables (`lemma_rels_keys`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::numeric::*;
use crate::spec::limits::*;
use crate::spec::datetime::*;
use crate::schema::schema_spec;
use crate::gendb_constraints::declared_db;
use crate::spec::constraints::constraints_hold;
use crate::gendb_entry::stores::{StoresView, stored_ok};
use crate::gendb_entry::bound_db;
use crate::link::query::*;
use crate::stores::facts::interface as fi;
use crate::stores::li_okruns::interface as lr;
use crate::stores::custpart::interface as ci;
use crate::stores::suppliers::interface as si;
use crate::stores::li_okruns::declaration as fd;
use crate::stores::custpart::declaration as cd;
use crate::stores::suppliers::declaration as sd;
use crate::agent::q5spec::*;
use crate::agent::sqlrow::*;
use crate::agent::lookup::*;

verus! {

/// The relations of the storage uses that the query does not read (part and partsupp).
pub open spec fn other_rels(db: Database) -> (Seq<Row>, Seq<Row>) {
    (cd::stored_relations(db)[1], sd::stored_relations(db)[0])
}

/// The parts of the storage uses read represent `rs` (and the unread part, partsupp relations): `li_okruns` is
/// facts' 75 parts (lineitem, orders) followed by the l_orderkey run starts; `facts` itself is not read.
pub open spec fn parts_rep(sv: StoresView, rs: Rels, part: Seq<Row>, psupp: Seq<Row>) -> bool {
    &&& lr::represents(sv.li_okruns, seq![rs.l, rs.o])
    &&& ci::represents(sv.custpart, seq![rs.c, part])
    &&& si::represents(sv.suppliers, seq![psupp, rs.s, rs.n, rs.r])
}

/// The column shapes the query reads, per stored relation.
pub open spec fn rels_shapes(rs: Rels) -> bool {
    &&& forall|i: int| 0 <= i < rs.l.len() ==> {
        let l = #[trigger] rs.l[i];
        &&& l.len() == 15 && is_int8(l[0]) && is_int8(l[2]) && is_num15(l[5]) && is_num15(l[6])
    }
    &&& forall|i: int| 0 <= i < rs.o.len() ==> {
        let o = #[trigger] rs.o[i];
        &&& o.len() == 7 && is_int8(o[0]) && is_int8(o[1]) && o[4] is Date && date_valid(o[4]->Date_0)
    }
    &&& forall|i: int| 0 <= i < rs.c.len() ==> {
        let c = #[trigger] rs.c[i];
        &&& c.len() == 8 && is_int8(c[0]) && is_int8(c[3])
    }
    &&& forall|i: int| 0 <= i < rs.s.len() ==> {
        let s = #[trigger] rs.s[i];
        &&& s.len() == 7 && is_int8(s[0]) && is_int8(s[3])
    }
    &&& forall|i: int| 0 <= i < rs.n.len() ==> {
        let n = #[trigger] rs.n[i];
        &&& n.len() == 4 && is_int8(n[0]) && n[1] is Text && is_int8(n[2])
    }
    &&& forall|i: int| 0 <= i < rs.r.len() ==> {
        let r = #[trigger] rs.r[i];
        &&& r.len() == 3 && is_int8(r[0]) && r[1] is Text
    }
}

/// The stored relations of the three storage uses are the query's relations.
pub proof fn lemma_storage_rels(db: Database)
    ensures
        fd::stored_relations(db) == seq![rels_of_db(db).l, rels_of_db(db).o],
        cd::stored_relations(db) == seq![rels_of_db(db).c, other_rels(db).0],
        sd::stored_relations(db) == seq![other_rels(db).1, rels_of_db(db).s, rels_of_db(db).n, rels_of_db(db).r],
{
    assert(fd::stored_cols_t0() == fcols6()[2]);
    assert(fd::stored_cols_t1() == fcols6()[1]);
    assert(cd::stored_cols_t0() == fcols6()[0]);
    assert(sd::stored_cols_t1() == fcols6()[3]);
    assert(sd::stored_cols_t2() == fcols6()[4]);
    assert(sd::stored_cols_t3() == fcols6()[5]);
    assert(fd::stored_relations(db) =~= seq![rels_of_db(db).l, rels_of_db(db).o]);
    assert(cd::stored_relations(db) =~= seq![rels_of_db(db).c, other_rels(db).0]);
    assert(sd::stored_relations(db) =~= seq![other_rels(db).1, rels_of_db(db).s, rels_of_db(db).n, rels_of_db(db).r]);
}

/// A bound database's parts represent its relations.
pub proof fn lemma_bound_rep(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures parts_rep(sv, rels_of_db(db), other_rels(db).0, other_rels(db).1),
{
    lemma_storage_rels(db);
}

/// The parts determine the relations: every bound database has the same stored relations.
pub proof fn lemma_rels_determined(sv: StoresView, db: Database, rs: Rels, part: Seq<Row>, psupp: Seq<Row>)
    requires bound_db(sv, db), parts_rep(sv, rs, part, psupp),
    ensures rels_of_db(db) == rs,
{
    lemma_bound_rep(sv, db);
    let r0 = rels_of_db(db);
    lr::lemma_represents_determines(sv.li_okruns, seq![r0.l, r0.o], seq![rs.l, rs.o]);
    ci::lemma_represents_determines(sv.custpart, seq![r0.c, other_rels(db).0], seq![rs.c, part]);
    si::lemma_represents_determines(sv.suppliers, seq![other_rels(db).1, r0.s, r0.n, r0.r], seq![psupp, rs.s, rs.n, rs.r]);
    assert(seq![r0.l, r0.o][0] == seq![rs.l, rs.o][0]);
    assert(seq![r0.l, r0.o][1] == seq![rs.l, rs.o][1]);
    assert(seq![r0.c, other_rels(db).0][0] == seq![rs.c, part][0]);
    assert(seq![other_rels(db).1, r0.s, r0.n, r0.r][1] == seq![psupp, rs.s, rs.n, rs.r][1]);
    assert(seq![other_rels(db).1, r0.s, r0.n, r0.r][2] == seq![psupp, rs.s, rs.n, rs.r][2]);
    assert(seq![other_rels(db).1, r0.s, r0.n, r0.r][3] == seq![psupp, rs.s, rs.n, rs.r][3]);
}

/// A NOT NULL date value.
proof fn lemma_date_value(v: Val)
    requires value_in_column(v, Column { ty: SqlType::Date, nullable: false }),
    ensures v is Date && date_valid(v->Date_0),
{
}

/// The relations of a well-formed database of the schema have the shapes the query reads.
pub proof fn lemma_rels_shapes(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures rels_shapes(rels_of_db(db)), rels_widths(rels_of_db(db)),
{
    let rs = rels_of_db(db);
    lemma_schema_cols();
    assert(schema_spec().len() == 8) by (compute);
    assert forall|i: int| 0 <= i < rs.l.len() implies {
        let l = #[trigger] rs.l[i];
        &&& l.len() == 15 && is_int8(l[0]) && is_int8(l[2]) && is_num15(l[5]) && is_num15(l[6])
    } by {
        let x = db.tables[0][i];
        assert(row_in_table(x, schema_spec()[0]));
        assert(rs.l[i] == proj(x, fcols6()[2]));
        assert(value_in_column(x[0], schema_spec()[0].columns[0]));
        assert(value_in_column(x[2], schema_spec()[0].columns[2]));
        assert(value_in_column(x[5], schema_spec()[0].columns[5]));
        assert(value_in_column(x[6], schema_spec()[0].columns[6]));
        lemma_num15_value(x[5]);
        lemma_num15_value(x[6]);
    }
    assert forall|i: int| 0 <= i < rs.o.len() implies {
        let o = #[trigger] rs.o[i];
        &&& o.len() == 7 && is_int8(o[0]) && is_int8(o[1]) && o[4] is Date && date_valid(o[4]->Date_0)
    } by {
        let x = db.tables[1][i];
        assert(row_in_table(x, schema_spec()[1]));
        assert(rs.o[i] == proj(x, fcols6()[1]));
        assert(value_in_column(x[0], schema_spec()[1].columns[0]));
        assert(value_in_column(x[1], schema_spec()[1].columns[1]));
        assert(value_in_column(x[4], schema_spec()[1].columns[4]));
        lemma_date_value(x[4]);
    }
    assert forall|i: int| 0 <= i < rs.c.len() implies {
        let c = #[trigger] rs.c[i];
        &&& c.len() == 8 && is_int8(c[0]) && is_int8(c[3])
    } by {
        let x = db.tables[2][i];
        assert(row_in_table(x, schema_spec()[2]));
        assert(rs.c[i] == proj(x, fcols6()[0]));
        assert(value_in_column(x[0], schema_spec()[2].columns[0]));
        assert(value_in_column(x[3], schema_spec()[2].columns[3]));
    }
    assert forall|i: int| 0 <= i < rs.s.len() implies {
        let s = #[trigger] rs.s[i];
        &&& s.len() == 7 && is_int8(s[0]) && is_int8(s[3])
    } by {
        let x = db.tables[5][i];
        assert(row_in_table(x, schema_spec()[5]));
        assert(rs.s[i] == proj(x, fcols6()[3]));
        assert(value_in_column(x[0], schema_spec()[5].columns[0]));
        assert(value_in_column(x[3], schema_spec()[5].columns[3]));
    }
    assert forall|i: int| 0 <= i < rs.n.len() implies {
        let n = #[trigger] rs.n[i];
        &&& n.len() == 4 && is_int8(n[0]) && n[1] is Text && is_int8(n[2])
    } by {
        let x = db.tables[6][i];
        assert(row_in_table(x, schema_spec()[6]));
        assert(rs.n[i] == proj(x, fcols6()[4]));
        assert(value_in_column(x[0], schema_spec()[6].columns[0]));
        assert(value_in_column(x[1], schema_spec()[6].columns[1]));
        assert(value_in_column(x[2], schema_spec()[6].columns[2]));
    }
    assert forall|i: int| 0 <= i < rs.r.len() implies {
        let r = #[trigger] rs.r[i];
        &&& r.len() == 3 && is_int8(r[0]) && r[1] is Text
    } by {
        let x = db.tables[7][i];
        assert(row_in_table(x, schema_spec()[7]));
        assert(rs.r[i] == proj(x, fcols6()[5]));
        assert(value_in_column(x[0], schema_spec()[7].columns[0]));
        assert(value_in_column(x[1], schema_spec()[7].columns[1]));
    }
}

/// The dimension relations of a database satisfying the declared keys have unique column 0.
pub proof fn lemma_rels_keys(db: Database)
    requires db.schema == schema_spec(), db_wf(db), constraints_hold(declared_db(db)),
    ensures
        keys_unique(rels_of_db(db).o), keys_unique(rels_of_db(db).c), keys_unique(rels_of_db(db).s),
        keys_unique(rels_of_db(db).n), keys_unique(rels_of_db(db).r),
{
    lemma_pk_unique(db, 1, fcols6()[1]);
    lemma_pk_unique(db, 2, fcols6()[0]);
    lemma_pk_unique(db, 5, fcols6()[3]);
    lemma_pk_unique(db, 6, fcols6()[4]);
    lemma_pk_unique(db, 7, fcols6()[5]);
}

} // verus!
