//! Reading the `lineitem` columns of Q6 from the flat storage, and their binding to every database the entry
//! quantifies over: for each bound `db`, `db.tables[0]` is the stored relation itself, every row is well formed
//! (`rows_ok`), and its projection onto `src_cols()` is the column view `crows(c)`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::numeric::{pow10, abs};
use crate::gendb_entry::stored::StoredParts;
use crate::link::query::*;
use crate::link::source::*;
use crate::schema::schema_spec;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_lineitem::declaration::*;
use crate::agent::normal::*;
use crate::agent::columns::*;

verus! {

/// Every row of the table is a well-formed `lineitem` row on the columns Q6 reads.
pub open spec fn rows_ok(rows: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> table_row_ok(#[trigger] rows[i])
}

/// Stored row `r` (16 columns) holds the column values of row `j` of `c`.
pub open spec fn row_matches(c: Cols, r: Row, j: int) -> bool {
    &&& r.len() == 16
    &&& r[4] == Val::Num { coeff: c.qty@[j] as int, scale: 2 }
    &&& r[5] == Val::Num { coeff: c.price@[j] as int, scale: 2 }
    &&& r[6] == Val::Num { coeff: c.disc@[j] as int, scale: 2 }
    &&& r[10] == Val::Date(day_of(c.ship@[j]))
}

/// The column slices are those of the stored relation `rel`, row for row.
pub open spec fn cols_match(c: Cols, rel: Seq<Row>) -> bool {
    &&& c.n == rel.len()
    &&& c.ship@.len() == c.n
    &&& c.disc@.len() == c.n
    &&& c.qty@.len() == c.n
    &&& c.price@.len() == c.n
    &&& forall|j: int| 0 <= j < c.n ==> row_matches(c, #[trigger] rel[j], j)
}

/// A numeric(15,2) value of the declared domain.
pub proof fn lemma_num15_2(v: Val)
    requires value_in_column(v, Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }),
    ensures num15_2(v),
{
    lemma_pow10_small();
    assert(abs(v->Num_coeff) < pow10(15));
}

/// Rows of the stored relation of a well-formed database are well-formed `lineitem` rows, and the summed factors
/// are numeric(15,2) coefficients.
pub proof fn lemma_rel_rows_ok(c: Cols, db: Database)
    requires
        db.schema == schema_spec(),
        db_wf(db),
        cols_match(c, stored_relations(db)[0]),
    ensures
        rows_ok(stored_relations(db)[0]),
        cols_wf(c),
{
    let rel = stored_relations(db)[0];
    lemma_stored_relations(db);
    let cs = stored_columns_t0();
    assert(cs[5] == Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false });
    assert(cs[6] == Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false });
    assert forall|j: int| 0 <= j < rel.len() implies table_row_ok(#[trigger] rel[j]) by {
        assert(row_matches(c, rel[j], j));
        assert(rel[j].len() == cs.len());
        lemma_num15_2(rel[j][5]);
        lemma_num15_2(rel[j][6]);
    }
    assert forall|j: int| 0 <= j < c.n implies coeff_ok(#[trigger] c.price@[j]) by {
        assert(row_matches(c, rel[j], j));
        assert(table_row_ok(rel[j]));
    }
    assert forall|j: int| 0 <= j < c.n implies coeff_ok(#[trigger] c.disc@[j]) by {
        assert(row_matches(c, rel[j], j));
        assert(table_row_ok(rel[j]));
    }
}

/// A stored row's projection onto the columns Q6 reads is the column view.
pub proof fn lemma_proj_matches(c: Cols, r: Row, j: int)
    requires row_matches(c, r, j),
    ensures proj(r, src_cols()) == crow(c, j),
{
    assert(proj(r, src_cols()) =~= crow(c, j));
}

/// The column view has `n` rows, row `i` being `crow(c, i)`.
pub proof fn lemma_crows(c: Cols)
    ensures
        crows(c).len() == c.n,
        forall|i: int| 0 <= i < c.n ==> #[trigger] crows(c)[i] == crow(c, i),
{
}

/// A bound database's `lineitem` table is the stored relation; its rows are well formed and project to the
/// column view.
pub proof fn lemma_db_rows(c: Cols, db: Database)
    requires
        db.schema == schema_spec(),
        db_wf(db),
        cols_match(c, stored_relations(db)[0]),
    ensures
        db.tables.len() > 0,
        db.tables[0] == stored_relations(db)[0],
        rows_ok(db.tables[0]),
        proj_all(db.tables[0], src_cols()) == crows(c),
        cols_wf(c),
{
    lemma_declared_schema();
    lemma_stored_relations(db);
    lemma_rel_rows_ok(c, db);
    let rows = db.tables[0];
    let rel = stored_relations(db)[0];
    assert(db.tables.len() == 8);
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] rows[j] == rel[j] by {
        assert(row_in_table(rows[j], db.schema[0]));
        lemma_proj_all_index(rows, stored_cols_t0());
        assert(rel[j] == proj(rows[j], stored_cols_t0()));
        assert(rows[j] =~= proj(rows[j], stored_cols_t0()));
    }
    assert(rows =~= rel);
    lemma_crows(c);
    assert forall|j: int| 0 <= j < c.n implies #[trigger] proj_all(rows, src_cols())[j] == crows(c)[j] by {
        assert(row_matches(c, rel[j], j));
        lemma_proj_matches(c, rel[j], j);
    }
    assert(proj_all(rows, src_cols()) =~= crows(c));
}

/// Reads the four columns of Q6 (whole parts) from the stored parts of `lineitem`.
pub fn read_cols(s: &mut StoredParts, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (c: Cols)
    requires li::represents(old(s)@, rels),
    ensures
        final(s)@ == old(s)@,
        cols_match(c, rels[0]),
{
    let ghost parts = s@;
    let n = li::stored_rows(s, Ghost(rels));
    let ship = li::read_l_shipdate(s, 0, n, Ghost(rels));
    let disc = li::read_l_discount(s, 0, n, Ghost(rels));
    let qty = li::read_l_quantity(s, 0, n, Ghost(rels));
    let price = li::read_l_extendedprice(s, 0, n, Ghost(rels));
    let c = Cols { ship, disc, qty, price, n };
    proof {
        assert forall|j: int| 0 <= j < c.n implies row_matches(c, #[trigger] rels[0][j], j) by {
            assert(rels[0][j] == li::row_at(parts, j));
            assert(rels[0][0 + j][4] == Val::Num { coeff: qty@[j] as int, scale: 2 });
            assert(rels[0][0 + j][5] == Val::Num { coeff: price@[j] as int, scale: 2 });
            assert(rels[0][0 + j][6] == Val::Num { coeff: disc@[j] as int, scale: 2 });
            assert(rels[0][0 + j][10] == crate::gendb_entry::source_check::date32_val(ship@[j]));
        }
    }
    c
}

} // verus!
