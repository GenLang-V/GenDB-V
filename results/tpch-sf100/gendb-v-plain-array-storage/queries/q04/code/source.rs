//! Reading the columns of Q4 from the flat storages, and their binding to every database the entry quantifies over:
//! for each bound `db`, `db.tables[0]` (`lineitem`) carries the `LCols` values (`li_rows_ok`) and `db.tables[1]`
//! (`orders`) is the stored `orders` relation itself, whose projection onto `src_cols()` is `crows(o)`.
//!
//! Fixed-width columns are read with the interface readers; the priority text column as whole parts (offsets and
//! bytes), so that row `i`'s value is `text_at` of the stored parts directly.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::typing::*;
use crate::gendb_entry::stored::StoredParts;
use crate::link::query::*;
use crate::link::source::*;
use crate::schema::schema_spec;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_lineitem::declaration as ld;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_orders::declaration as od;
use crate::agent::cols::*;
use crate::agent::normal::*;
use crate::agent::body::rows_ok;

verus! {

/// The stored `orders` relation carries the `OCols` values, row for row.
pub open spec fn o_match(o: OCols, rel: Seq<Row>) -> bool {
    &&& o.no == rel.len()
    &&& forall|i: int| 0 <= i < o.no ==> {
        &&& (#[trigger] rel[i]).len() == 9
        &&& rel[i][0] == Val::Int(o.okey@[i] as int)
        &&& rel[i][4] == Val::Date(o.odate@[i] - 10957)
        &&& rel[i][5] == Val::Text(prio(o, i))
    }
}

/// Reads `l_orderkey`, `l_commitdate`, `l_receiptdate` (whole columns).
pub fn read_lcols(s: &mut StoredParts, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (l: LCols)
    requires li::represents(old(s)@, rels),
    ensures
        final(s)@ == old(s)@,
        lcols_wf(l),
        li_rows_ok(rels[0], l),
{
    let ghost parts = s@;
    let nl = li::stored_rows(s, Ghost(rels));
    let lk = li::read_l_orderkey(s, 0, nl, Ghost(rels));
    let cm = li::read_l_commitdate(s, 0, nl, Ghost(rels));
    let rc = li::read_l_receiptdate(s, 0, nl, Ghost(rels));
    let l = LCols { lk, cm, rc, nl };
    proof {
        assert forall|j: int| 0 <= j < rels[0].len() implies {
            &&& (#[trigger] rels[0][j]).len() == 16
            &&& rels[0][j][0] == Val::Int(l.lk@[j] as int)
            &&& rels[0][j][11] == Val::Date(l.cm@[j] - 10957)
            &&& rels[0][j][12] == Val::Date(l.rc@[j] - 10957)
        } by {
            assert(rels[0][j] == li::row_at(parts, j));
            assert(rels[0][0 + j][0] == Val::Int(lk@[j] as int));
            assert(rels[0][0 + j][11] == crate::gendb_entry::source_check::date32_val(cm@[j]));
            assert(rels[0][0 + j][12] == crate::gendb_entry::source_check::date32_val(rc@[j]));
        }
    }
    l
}

/// Reads `o_orderkey`, `o_orderdate` and the parts of `o_orderpriority` (whole columns).
pub fn read_ocols(s: &mut StoredParts, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (o: OCols)
    requires oi::represents(old(s)@, rels),
    ensures
        final(s)@ == old(s)@,
        ocols_wf(o),
        o_match(o, rels[0]),
{
    let ghost parts = s@;
    let no = oi::stored_rows(s, Ghost(rels));
    let okey = oi::read_o_orderkey(s, 0, no, Ghost(rels));
    let odate = oi::read_o_orderdate(s, 0, no, Ghost(rels));
    let plen = s.part_len(oi::O_ORDERPRIORITY_OFFSETS);
    let poff = s.extent_i64(oi::O_ORDERPRIORITY_OFFSETS, 0, plen);
    let blen = s.part_len(oi::O_ORDERPRIORITY_BYTES);
    let pbytes = s.extent_u8(oi::O_ORDERPRIORITY_BYTES, 0, blen);
    let o = OCols { okey, odate, poff, pbytes, no };
    proof {
        let tv = oi::text_view(parts, oi::O_ORDERPRIORITY_OFFSETS as int, oi::O_ORDERPRIORITY_BYTES as int);
        assert(poff@ =~= tv.offsets);
        assert(pbytes@ =~= tv.bytes);
        assert(pview(o) == tv);
        assert forall|i: int| 0 <= i < o.no implies {
            &&& (#[trigger] rels[0][i]).len() == 9
            &&& rels[0][i][0] == Val::Int(o.okey@[i] as int)
            &&& rels[0][i][4] == Val::Date(o.odate@[i] - 10957)
            &&& rels[0][i][5] == Val::Text(prio(o, i))
        } by {
            assert(rels[0][i] == oi::row_at(parts, i));
            assert(rels[0][0 + i][0] == Val::Int(okey@[i] as int));
            assert(rels[0][0 + i][4] == crate::gendb_entry::source_check::date32_val(odate@[i]));
        }
    }
    o
}

/// A row of a table that stores every column in order is its own projection on those columns.
pub proof fn lemma_full_proj(r: Row, n: nat, cols: Seq<nat>)
    requires r.len() == n, cols.len() == n, forall|k: int| 0 <= k < n ==> #[trigger] cols[k] == k,
    ensures proj(r, cols) == r,
{
    assert(proj(r, cols) =~= r);
}

/// A bound database's `lineitem` table carries the values of `l`.
pub proof fn lemma_db_lineitem(db: Database, l: LCols)
    requires
        db.schema == schema_spec(),
        db_wf(db),
        li_rows_ok(ld::stored_relations(db)[0], l),
    ensures
        db.tables.len() == 8,
        li_rows_ok(db.tables[0], l),
{
    ld::lemma_declared_schema();
    ld::lemma_stored_relations(db);
    let rows = db.tables[0];
    let rel = ld::stored_relations(db)[0];
    let cols = ld::stored_cols_t0();
    assert(db.tables.len() == 8);
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] rows[j] == rel[j] by {
        assert(row_in_table(rows[j], db.schema[0]));
        lemma_proj_all_index(rows, cols);
        assert forall|k: int| 0 <= k < 16 implies #[trigger] cols[k] == k by {}
        lemma_full_proj(rows[j], 16, cols);
    }
    assert(rows =~= rel);
}

/// A bound database's `orders` table is the stored relation: well-formed rows projecting to `crows(o)`.
pub proof fn lemma_db_orders(db: Database, o: OCols)
    requires
        db.schema == schema_spec(),
        db_wf(db),
        o_match(o, od::stored_relations(db)[0]),
    ensures
        db.tables.len() == 8,
        rows_ok(db.tables[1]),
        proj_all(db.tables[1], src_cols()) == crows(o),
{
    od::lemma_declared_schema();
    od::lemma_stored_relations(db);
    let rows = db.tables[1];
    let rel = od::stored_relations(db)[0];
    let cols = od::stored_cols_t0();
    assert(db.tables.len() == 8);
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] rows[j] == rel[j] by {
        assert(row_in_table(rows[j], db.schema[1]));
        lemma_proj_all_index(rows, cols);
        assert forall|k: int| 0 <= k < 9 implies #[trigger] cols[k] == k by {}
        lemma_full_proj(rows[j], 9, cols);
    }
    assert(rows =~= rel);
    assert forall|i: int| 0 <= i < rows.len() implies o_row_ok(#[trigger] rows[i]) by {
        assert(rel[i].len() == 9);
    }
    let xs = proj_all(rows, src_cols());
    lemma_proj_all_index(rows, src_cols());
    assert forall|i: int| 0 <= i < o.no implies #[trigger] xs[i] == crows(o)[i] by {
        assert(rel[i].len() == 9);
        assert(xs[i] =~= crow(o, i));
    }
    assert(xs =~= crows(o));
}

} // verus!
