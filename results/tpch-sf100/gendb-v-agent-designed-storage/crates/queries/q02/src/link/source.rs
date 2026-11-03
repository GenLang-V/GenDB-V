//! Source relations. A source table is delivered as the declared columns `cols` of every row of `db.tables[t]`, in
//! row order: `link::query::proj_all(db.tables[t], cols)`. The generated source file of a candidate states its
//! binding with `proj_columns`, `rows_in_columns` and `cols_in_table`, so those definitions are part of the fixed
//! meaning (`link` module doc). `lemma_source_in_domain`: on a well-formed database (`db_wf`) every delivered value
//! lies in its declared column's domain (type, NOT NULL, integer range, numeric scale and precision).
//!
//! A storage stores a table's declared columns `cols` as the relation `proj_all(db.tables[t], cols)` (generated
//! `stores/<name>/declaration.rs`); a query that reads the positions `pos` of that relation reads the table's columns
//! `compose_cols(cols, pos)` (`lemma_proj_all_compose`), so a storage of more columns than a query demands serves it.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::link::query::{proj, proj_all};

verus! {

/// The declared columns `cols` of table schema `ts`, in that order.
pub open spec fn proj_columns(ts: TableSchema, cols: Seq<nat>) -> Seq<Column> {
    Seq::new(cols.len(), |k: int| ts.columns[cols[k] as int])
}

/// Every row has one value per column, each in its column's domain.
pub open spec fn rows_in_columns(rows: Seq<Row>, cs: Seq<Column>) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> {
        &&& #[trigger] rows[i].len() == cs.len()
        &&& forall|k: int| 0 <= k < cs.len() ==> value_in_column(#[trigger] rows[i][k], cs[k])
    }
}

/// Every declared column exists in the table.
pub open spec fn cols_in_table(ts: TableSchema, cols: Seq<nat>) -> bool {
    forall|k: int| 0 <= k < cols.len() ==> #[trigger] cols[k] < ts.columns.len()
}

/// Length and values of a projected relation, by index.
pub proof fn lemma_proj_all_index(rows: Seq<Row>, cols: Seq<nat>)
    ensures
        proj_all(rows, cols).len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] proj_all(rows, cols)[i]) == proj(rows[i], cols),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] proj_all(rows, cols)[i]).len() == cols.len(),
        forall|i: int, k: int| 0 <= i < rows.len() && 0 <= k < cols.len()
            ==> #[trigger] proj_all(rows, cols)[i][k] == rows[i][cols[k] as int],
{
}

/// The table columns that positions `pos` of a projection onto `cols` read.
pub open spec fn compose_cols(cols: Seq<nat>, pos: Seq<nat>) -> Seq<nat> {
    Seq::new(pos.len(), |k: int| cols[pos[k] as int])
}

/// Projecting a projection: positions `pos` of the rows projected onto `cols` are the rows projected onto
/// `compose_cols(cols, pos)`.
pub proof fn lemma_proj_all_compose(rows: Seq<Row>, cols: Seq<nat>, pos: Seq<nat>)
    requires forall|k: int| 0 <= k < pos.len() ==> #[trigger] pos[k] < cols.len(),
    ensures proj_all(proj_all(rows, cols), pos) == proj_all(rows, compose_cols(cols, pos)),
{
    let (inner, outer, direct) = (proj_all(rows, cols), proj_all(proj_all(rows, cols), pos), proj_all(rows, compose_cols(cols, pos)));
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] outer[i] == direct[i] by {
        assert(inner[i] == proj(rows[i], cols));
        assert(outer[i] =~= proj(rows[i], compose_cols(cols, pos)));
    }
    assert(outer =~= direct);
}

/// The delivered columns of a table of a well-formed database are in their declared columns' domains.
pub proof fn lemma_source_in_domain(db: Database, t: nat, cols: Seq<nat>)
    requires db_wf(db), t < db.tables.len(), cols_in_table(db.schema[t as int], cols),
    ensures rows_in_columns(proj_all(db.tables[t as int], cols), proj_columns(db.schema[t as int], cols)),
{
    let rows = db.tables[t as int];
    let ts = db.schema[t as int];
    lemma_proj_all_index(rows, cols);
    assert forall|i: int| 0 <= i < rows.len() implies {
        &&& #[trigger] proj_all(rows, cols)[i].len() == proj_columns(ts, cols).len()
        &&& forall|k: int| 0 <= k < proj_columns(ts, cols).len()
            ==> value_in_column(#[trigger] proj_all(rows, cols)[i][k], proj_columns(ts, cols)[k])
    } by {
        assert(row_in_table(rows[i], ts));
        assert forall|k: int| 0 <= k < proj_columns(ts, cols).len()
            implies value_in_column(#[trigger] proj_all(rows, cols)[i][k], proj_columns(ts, cols)[k]) by {
            assert(cols[k] < ts.columns.len());
            assert(proj_all(rows, cols)[i][k] == rows[i][cols[k] as int]);
        }
    }
}

} // verus!
