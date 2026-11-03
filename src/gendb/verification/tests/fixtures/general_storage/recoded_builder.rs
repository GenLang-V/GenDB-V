//! TEST FIXTURE (general engine line; framework test only, not an author output): the builder of storage `recoded`,
//! built from the flat storage of its table (no `extends`: it writes its own part). It reads the column through the
//! generated `crate::sources_flat` (by table id and column ordinal; no table or column name) and narrows every 128-bit
//! coefficient to 64 bits: the declared precision keeps each coefficient within 64 bits.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::layout::{owned_parts_view, PartView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::Stores;
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::link::source::{lemma_proj_all_index, proj_columns};
use crate::schema::schema_spec;
use crate::sources_flat::{column_slice, lemma_flat_table_unique, table_rows, ColumnSlice};
use crate::spec::numeric::pow10;
use crate::spec::typing::{row_in_table, value_in_column};
use crate::spec::value::{Database, Val};
use crate::stores::recoded::declaration::{lemma_declared_schema, stored_cols_t0, stored_columns_t0, stored_table_t0};
use crate::stores::recoded::interface::scale;

verus! {

/// The table and the column the storage holds, by id (the storage's declaration states the same).
pub const TABLE: usize = 0;
pub const COLUMN: usize = 5;

/// What the declaration states: table `TABLE` and its one column `COLUMN`, of the schema's numeric type, whose precision
/// keeps every coefficient within 64 bits.
proof fn lemma_declared()
    ensures
        stored_table_t0() == TABLE as nat,
        stored_cols_t0() == seq![COLUMN as nat],
        schema_spec()[TABLE as int].columns[COLUMN as int] == stored_columns_t0()[0],
        stored_columns_t0()[0].ty is Numeric,
        pow10(stored_columns_t0()[0].ty->Numeric_precision as nat) <= 0x7fff_ffff_ffff_ffffint,
{
    lemma_declared_schema();
    assert(stored_cols_t0() =~= seq![COLUMN as nat]);
    assert(proj_columns(schema_spec()[TABLE as int], stored_cols_t0())[0] == schema_spec()[TABLE as int].columns[COLUMN as int]);
    assert(pow10(stored_columns_t0()[0].ty->Numeric_precision as nat) <= 0x7fff_ffff_ffff_ffffint) by (compute);
}

/// Copy the column into one 64-bit part (the derived storage entry's builder).
#[verifier::loop_isolation(false)]
pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> forall|db: Database| #[trigger] sources_bound(old(stores)@, db)
            ==> represents(storage_parts(old(stores)@, owned_parts_view(p@)), stored_relations(db)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost sv = stores@;
    let ghost db = choose|db: Database| sources_bound(sv, db);
    proof {
        lemma_declared();
    }
    let n = table_rows(stores, TABLE, Ghost(db));
    let mut out: Vec<i64> = Vec::new();
    if n > 0 {
        let lo: usize = 0;
        let s = column_slice(stores, TABLE, COLUMN, lo, n, Ghost(db));
        match s {
            ColumnSlice::Numeric(v, s_scale) => {
                let mut i: usize = 0;
                while i < n
                    invariant
                        i <= n,
                        stores@ == sv,
                        out@.len() == i,
                        forall|k: int| 0 <= k < i ==> #[trigger] db.tables[TABLE as int][k][COLUMN as int]
                            == (Val::Num { coeff: out@[k] as int, scale: scale() }),
                    decreases n - i,
                {
                    let ghost row = db.tables[TABLE as int][i as int];
                    proof {
                        assert(db.tables[TABLE as int][lo as int + i as int][COLUMN as int] == Val::Num { coeff: v@[i as int] as int, scale: s_scale as nat });
                        assert(row_in_table(row, db.schema[TABLE as int]));
                        assert(value_in_column(row[COLUMN as int], db.schema[TABLE as int].columns[COLUMN as int]));
                        assert(scale() == s_scale as nat);
                    }
                    out.push(v[i] as i64);
                    i += 1;
                }
            },
            _ => {
                proof {
                    assert(false);
                }
            },
        }
    }
    let parts: Vec<OwnedPart> = vec![OwnedPart::I64(out)];
    proof {
        assert forall|other: Database| #[trigger] sources_bound(sv, other)
            implies represents(storage_parts(sv, owned_parts_view(parts@)), stored_relations(other)) by {
            lemma_flat_table_unique(sv, db, other, TABLE as int);
            assert(storage_parts(sv, owned_parts_view(parts@)) =~= seq![PartView::I64(out@)]);
            let rels = stored_relations(other);
            lemma_proj_all_index(other.tables[TABLE as int], stored_cols_t0());
            assert forall|i: int| 0 <= i < rels[0].len() implies #[trigger] rels[0][i]
                == seq![Val::Num { coeff: out@[i] as int, scale: scale() }] by {
                assert(rels[0][i][0] == other.tables[TABLE as int][i][COLUMN as int]);
                assert(rels[0][i] =~= seq![rels[0][i][0]]);
            }
        }
    }
    Ok(parts)
}

} // verus!
