//! TEST FIXTURE (general engine line; framework test only, not an author output): the builder of storage `zoned`,
//! built from the flat storage of its table and extending it: the flat parts are kept unchanged, and the builder adds
//! the zone part (the smallest key). It reads the keys through the generated `crate::sources_flat` and restates the
//! kept parts with `lemma_flat_plain` (by table id; no table or column name).
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::layout::{owned_parts_view, PartView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::Stores;
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::link::source::proj_columns;
use crate::schema::schema_spec;
use crate::sources_flat::{column_slice, flat_layout, flat_part_count, flat_parts, lemma_flat_plain, lemma_flat_table_unique, table_rows, ColumnSlice};
use crate::spec::value::{Database, Val};
use crate::stores::zoned::declaration::{lemma_declared_schema, stored_cols_t0, stored_columns_t0, stored_table_t0};
use crate::stores::zoned::interface::{layout, zone_holds, ZONE};

verus! {

/// The table the storage keeps, by id (the storage's declaration states the same).
pub const TABLE: usize = 7;

/// What the declaration states: table `TABLE` and all of its columns in order, so its column types are the schema's
/// and its part layout is the flat storage's.
proof fn lemma_declared()
    ensures
        stored_table_t0() == TABLE as nat,
        stored_columns_t0() == schema_spec()[TABLE as int].columns,
        stored_cols_t0().len() == 3,
        forall|k: int| 0 <= k < 3 ==> #[trigger] stored_cols_t0()[k] == k,
        layout() == flat_layout(TABLE as int),
{
    lemma_declared_schema();
    let cols = stored_cols_t0();
    assert(cols =~= seq![0nat, 1nat, 2nat]);
    assert forall|k: int| 0 <= k < 3 implies #[trigger] cols[k] == k by {
        if k == 0 {} else if k == 1 {} else {}
    }
    assert(proj_columns(schema_spec()[TABLE as int], cols) =~= schema_spec()[TABLE as int].columns);
    assert forall|k: int| 0 <= k < 3 implies #[trigger] layout()[k] == flat_layout(TABLE as int)[k] by {
        if k == 0 {} else if k == 1 {} else {}
    }
    assert(layout() =~= flat_layout(TABLE as int));
}

/// Keep the flat parts, add the zone part (the derived storage entry's builder).
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
    let ghost flat = flat_parts(sv, TABLE as int);
    proof {
        lemma_declared();
        lemma_flat_plain(sv, db, TABLE as int);
        assert(crate::sources_flat::plain::plain_column(flat, flat_layout(TABLE as int)[0], schema_spec()[TABLE as int].columns[0].ty, db.tables[TABLE as int], 0));
    }
    let n = table_rows(stores, TABLE, Ghost(db));
    proof {
        // The key column (0, an integer) is held in part 0 of the flat parts, one value per row.
        assert(flat_layout(TABLE as int)[0] == 0);
        assert(stored_columns_t0()[0].ty is Int8);
        assert(flat[0] is I64 && flat[0]->I64_0.len() == n);
    }
    let mut zone: Vec<i64> = Vec::new();
    if n > 0 {
        let lo: usize = 0;
        let s = column_slice(stores, TABLE, 0, lo, n, Ghost(db));
        match s {
            ColumnSlice::Int64(keys) => {
                let mut smallest = keys[0];
                let mut i: usize = 1;
                while i < n
                    invariant
                        1 <= i <= n,
                        keys@.len() == n,
                        forall|k: int| 0 <= k < i ==> smallest <= #[trigger] keys@[k],
                    decreases n - i,
                {
                    if keys[i] < smallest {
                        smallest = keys[i];
                    }
                    i += 1;
                }
                zone.push(smallest);
                proof {
                    assert forall|j: int| 0 <= j < n implies #[trigger] keys@[j] == flat[0]->I64_0[j] by {
                        assert(db.tables[TABLE as int][lo as int + j][0] == Val::Int(keys@[j] as int));
                        assert(db.tables[TABLE as int][j][0] == Val::Int(flat[0]->I64_0[j] as int));
                    }
                    assert(zone@ =~= seq![smallest]);
                    assert forall|j: int| 0 <= j < flat[0]->I64_0.len() implies zone@[0] <= #[trigger] flat[0]->I64_0[j] by {
                        assert(keys@[j] == flat[0]->I64_0[j]);
                        assert(smallest <= keys@[j]);
                    }
                }
            },
            _ => {
                proof {
                    assert(false);
                }
            },
        }
    }
    proof {
        assert(zone_holds(zone@, flat[0]->I64_0));
    }
    let parts: Vec<OwnedPart> = vec![OwnedPart::I64(zone)];
    proof {
        let all = storage_parts(sv, owned_parts_view(parts@));
        assert(all =~= flat + seq![PartView::I64(zone@)]);
        assert(flat.len() == flat_part_count(TABLE as int));
        assert forall|other: Database| #[trigger] sources_bound(sv, other) implies represents(all, stored_relations(other)) by {
            lemma_flat_table_unique(sv, db, other, TABLE as int);
            let rows = other.tables[TABLE as int];
            let cols = stored_columns_t0();
            crate::stores::zoned::interface::plain::lemma_proj_identity(rows, stored_cols_t0(), 3);
            assert(stored_relations(other)[0] == rows);
            assert forall|k: int| 0 <= k < cols.len() implies #[trigger] crate::stores::zoned::interface::plain::plain_column(all, layout()[k], cols[k].ty, rows, k) by {
                let p = layout()[k];
                assert(crate::sources_flat::plain::plain_column(flat, flat_layout(TABLE as int)[k], schema_spec()[TABLE as int].columns[k].ty, rows, k));
                assert(all[p] == flat[p]);
                if p + 1 < flat.len() {
                    assert(all[p + 1] == flat[p + 1]);
                }
            }
            assert(all[ZONE as int] == PartView::I64(zone@));
            assert(all[0] == flat[0]);
        }
    }
    Ok(parts)
}

} // verus!
