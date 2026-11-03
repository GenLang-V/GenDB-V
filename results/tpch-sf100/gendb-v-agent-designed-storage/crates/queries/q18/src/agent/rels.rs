//! The tables of a database bound to the parts, projected on the columns Q18 reads (`lrel`, `orel`, `crel`), and
//! sums over them as index sums over the model (`lemma_sum_l`, `lemma_sum_o`, `lemma_sum_c`): lineitem and orders are
//! the model's stored rows through their row maps (permutations), customer is in canonical order. Also the row
//! widths of the three tables and the decoded values of a canonical lineitem row.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::typing::{db_wf, row_in_table};
use crate::spec::numeric::pow10;
use crate::schema::schema_spec;
use crate::link::query::*;
use crate::link::join::{sum_of, lemma_sum_of_perm};
use crate::link::source::lemma_proj_all_index;
use crate::stores::liruns::interface::common::colfmt as ff;
use super::common::isum::*;
use super::model::*;

verus! {

/// The database facts the links need.
pub open spec fn db_ok(db: Database) -> bool {
    db.schema == schema_spec() && db_wf(db)
}

pub open spec fn crel(db: Database) -> Seq<Row> { proj_all(db.tables[2], ccols()) }
pub open spec fn orel(db: Database) -> Seq<Row> { proj_all(db.tables[1], ocols()) }
pub open spec fn lrel(db: Database) -> Seq<Row> { proj_all(db.tables[0], lcols()) }

/// Row widths of the three tables.
pub proof fn lemma_widths(db: Database)
    requires db_ok(db),
    ensures
        db.tables.len() == 8,
        forall|i: int| 0 <= i < db.tables[2].len() ==> (#[trigger] db.tables[2][i]).len() == 8,
        forall|i: int| 0 <= i < db.tables[1].len() ==> (#[trigger] db.tables[1][i]).len() == 9,
        forall|i: int| 0 <= i < db.tables[0].len() ==> (#[trigger] db.tables[0][i]).len() == 16,
{
    crate::stores::liruns::declaration::lemma_declared_schema();
    assert(schema_spec()[2].columns.len() == 8) by (compute);
    assert forall|i: int| 0 <= i < db.tables[2].len() implies (#[trigger] db.tables[2][i]).len() == 8 by {
        assert(row_in_table(db.tables[2][i], db.schema[2]));
    }
    assert forall|i: int| 0 <= i < db.tables[1].len() implies (#[trigger] db.tables[1][i]).len() == 9 by {
        assert(row_in_table(db.tables[1][i], db.schema[1]));
    }
    assert forall|i: int| 0 <= i < db.tables[0].len() implies (#[trigger] db.tables[0][i]).len() == 16 by {
        assert(row_in_table(db.tables[0][i], db.schema[0]));
    }
}

/// A canonical lineitem row is the model row of the stored row that maps to it.
pub proof fn lemma_lrow_at(db: Database, m: M, i: int) -> (j: int)
    requires rel_ok(m, db), model_ok(m), 0 <= i < db.tables[0].len(),
    ensures
        0 <= j < m.l_n,
        m.l_map[j] == i,
        proj(db.tables[0][i], lcols()) == lrow(m, j),
        db.tables[0][i][0] == Val::Int(lkey(m, j)),
        db.tables[0][i][4] == (Val::Num { coeff: lqty(m, j), scale: 2 }),
        lrel(db)[i] == lrow(m, j),
        in_i64(lkey(m, j)),
        -pow10(15) < lqty(m, j) < pow10(15),
{
    assert(ff::covered(m.l_map, i));
    let j = choose|j: int| 0 <= j < m.l_map.len() && m.l_map[j] == i;
    let r = db.tables[0][i];
    assert(proj(r, lcols()) == lrow(m, j));
    assert(proj(r, lcols())[0] == r[0] && proj(r, lcols())[1] == r[4]);
    lemma_proj_all_index(db.tables[0], lcols());
    j
}

/// A sum over the lineitem relation is a sum over the model's stored rows (a permutation of it).
pub proof fn lemma_sum_l(db: Database, m: M, h: spec_fn(Row) -> int)
    requires rel_ok(m, db),
    ensures sum_of(lrel(db), h) == isum(m.l_n, |j: int| h(lrow(m, j))),
{
    let t = db.tables[0];
    let lr = lrel(db);
    lemma_proj_all_index(t, lcols());
    let st = ff::stored_rows(lr, m.l_map);
    assert(st =~= Seq::new(m.l_n as nat, |j: int| lrow(m, j))) by {
        assert forall|j: int| 0 <= j < m.l_n implies #[trigger] st[j] == lrow(m, j) by {
            assert(0 <= m.l_map[j] < m.l_n);
        }
    }
    ff::lemma_stored_rows_multiset(lr, m.l_map);
    lemma_sum_of_perm(st, lr, h);
    lemma_sum_of_seq(m.l_n, |j: int| lrow(m, j), h);
    lemma_isum_ext(m.l_n, |i: int| h((|j: int| lrow(m, j))(i)), |j: int| h(lrow(m, j)));
}

/// A sum over the orders relation is a sum over the model's stored positions.
pub proof fn lemma_sum_o(db: Database, m: M, h: spec_fn(Row) -> int)
    requires rel_ok(m, db),
    ensures sum_of(orel(db), h) == isum(m.o_n, |q: int| h(orow(m, q))),
{
    let t = db.tables[1];
    let orr = orel(db);
    lemma_proj_all_index(t, ocols());
    let st = ff::stored_rows(orr, m.o_map);
    assert(st =~= Seq::new(m.o_n as nat, |q: int| orow(m, q))) by {
        assert forall|q: int| 0 <= q < m.o_n implies #[trigger] st[q] == orow(m, q) by {
            assert(0 <= m.o_map[q] < m.o_n);
        }
    }
    ff::lemma_stored_rows_multiset(orr, m.o_map);
    lemma_sum_of_perm(st, orr, h);
    lemma_sum_of_seq(m.o_n, |q: int| orow(m, q), h);
    lemma_isum_ext(m.o_n, |i: int| h((|q: int| orow(m, q))(i)), |q: int| h(orow(m, q)));
}

/// A sum over the customer relation (canonical order) is a sum over the model's rows.
pub proof fn lemma_sum_c(db: Database, m: M, h: spec_fn(Row) -> int)
    requires rel_ok(m, db),
    ensures sum_of(crel(db), h) == isum(m.c_n, |c: int| h(crow(m, c))),
{
    let t = db.tables[2];
    lemma_proj_all_index(t, ccols());
    assert(crel(db) =~= Seq::new(m.c_n as nat, |c: int| crow(m, c)));
    lemma_sum_of_seq(m.c_n, |c: int| crow(m, c), h);
    lemma_isum_ext(m.c_n, |i: int| h((|c: int| crow(m, c))(i)), |c: int| h(crow(m, c)));
}

} // verus!
