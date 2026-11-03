//! TEST FIXTURE (general engine line; framework test only, not an author output): version 0 that also reads two
//! storages built from flat storages. It materializes every table from its flat storage (`crate::flat_tables`), then
//! replaces the column storage `recoded` holds (through its reader) and column `ZONED_COLUMN` of the table storage
//! `zoned` keeps (through `zoned`'s plain-columns reader) by the values read from those storages, and answers with the
//! verified interpreter. Its proof links each storage to the bound database through the engine entry's `stored_ok`
//! and the storage's `represents`. It names no table or column (ids only).
use vstd::prelude::*;
use crate::gendb_entry::{answer_meets, bound_db, outcome_ok, stores_ready, supported, Answer};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::schema_exec::schema_exec;
use crate::exec::ast::{view_ordered, EOrderedQuery};
use crate::exec::value::{view_row, ERow, EVal};
use crate::exec::relational::rows::clone_row;
use crate::exec::relational::schema::{lemma_db_wf_ts_ok, view_rows, view_schema, view_table_schema, EDatabase};
use crate::exec::relational::entry::exec_ordered;
use crate::bridge::order::lemma_denote_top_ok;
use crate::flat_tables::{lemma_flat_database_unique, materialize_table};
use crate::link::source::lemma_proj_all_index;
use crate::schema::schema_spec;
use crate::spec::typing::row_in_table;
use crate::spec::value::{Database, Val};
use crate::stores::zoned::interface::plain::{plain_value, read_plain, PlainSlice};

verus! {

/// The table and column storage `recoded` holds, and the table storage `zoned` keeps with the column read from it.
pub const RECODED_TABLE: usize = 0;
pub const RECODED_COLUMN: usize = 5;
pub const ZONED_TABLE: usize = 7;
pub const ZONED_COLUMN: usize = 1;

/// The engine: version 0's answer over a database whose two columns are read from the derived storages.
pub fn engine(stores: &mut Stores, q: &EOrderedQuery, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        supported(view_ordered(*q)),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, view_ordered(*q), r),
{
    let ghost sv = stores@;
    let ghost db = choose|db: Database| bound_db(sv, db);
    let edb = materialize(stores, Ghost(db));
    proof {
        lemma_db_wf_ts_ok(db);
        lemma_denote_top_ok(db, view_ordered(*q));
    }
    let r: Result<Answer, QueryError> = match exec_ordered(&edb, q) {
        Ok(Ok(rows)) => {
            proof {
                assert(crate::link::query::view_rows(rows@) =~= view_rows(rows@));
            }
            Ok(Answer::Rows(rows))
        },
        Ok(Err(e)) => Ok(Answer::SqlError(e)),
        Err(_) => Ok(Answer::Capacity),
    };
    proof {
        assert forall|other: Database| #[trigger] bound_db(sv, other) implies outcome_ok(other, view_ordered(*q), r) by {
            lemma_flat_database_unique(sv, db, other);
        }
    }
    r
}

/// Every table, two columns of them read from the derived storages: `edb@ == db`.
fn materialize(stores: &mut Stores, Ghost(db): Ghost<Database>) -> (edb: EDatabase)
    requires
        bound_db(old(stores)@, db),
    ensures
        final(stores)@ == old(stores)@,
        edb@ == db,
{
    let t0 = materialize_table(stores, 0, Ghost(db));
    let t0 = replace_recoded(stores, t0, Ghost(db));
    let t1 = materialize_table(stores, 1, Ghost(db));
    let t2 = materialize_table(stores, 2, Ghost(db));
    let t3 = materialize_table(stores, 3, Ghost(db));
    let t4 = materialize_table(stores, 4, Ghost(db));
    let t5 = materialize_table(stores, 5, Ghost(db));
    let t6 = materialize_table(stores, 6, Ghost(db));
    let t7 = materialize_table(stores, 7, Ghost(db));
    let t7 = replace_zoned(stores, t7, Ghost(db));
    let tables: Vec<Vec<ERow>> = vec![t0, t1, t2, t3, t4, t5, t6, t7];
    let edb = EDatabase { schema: schema_exec(), tables };
    proof {
        crate::stores::recoded::declaration::lemma_declared_schema();
        assert(edb@.tables =~= db.tables);
        assert(edb@ == db);
    }
    edb
}

/// Row `j` of a text column read as `(offsets, bytes)` (the offsets as stored, the bytes from `offsets[0]`), copied.
fn text_value(offsets: &[i64], bytes: &[u8], j: usize) -> (v: EVal)
    requires
        j + 1 < offsets@.len(),
        0 <= offsets@[0],
        forall|a: int, b: int| 0 <= a <= b < offsets@.len() ==> offsets@[a] <= offsets@[b],
        bytes@.len() == offsets@[offsets@.len() - 1] - offsets@[0],
    ensures
        v@ == Val::Text(bytes@.subrange(offsets@[j as int] - offsets@[0], offsets@[j + 1] - offsets@[0])),
{
    let last = offsets.len() - 1;
    let size = bytes.len();
    assert(offsets@[0] <= offsets@[j as int] <= offsets@[j + 1] <= offsets@[last as int]);
    let (first, start, end) = (offsets[0], offsets[j], offsets[j + 1]);
    assert(0 <= start - first <= end - first <= size);
    let lo = (start - first) as usize;
    let hi = (end - first) as usize;
    let mut out: Vec<u8> = Vec::with_capacity(hi - lo);
    let mut i = lo;
    while i < hi
        invariant
            lo <= i <= hi <= bytes@.len(),
            out@ == bytes@.subrange(lo as int, i as int),
        decreases hi - i,
    {
        out.push(bytes[i]);
        i += 1;
        assert(out@ =~= bytes@.subrange(lo as int, i as int));
    }
    EVal::Text(out)
}

/// `rows` (table `RECODED_TABLE` as materialized) with column `RECODED_COLUMN` read from storage `recoded`.
#[verifier::loop_isolation(false)]
fn replace_recoded(stores: &mut Stores, rows: Vec<ERow>, Ghost(db): Ghost<Database>) -> (out: Vec<ERow>)
    requires
        bound_db(old(stores)@, db),
        view_rows(rows@) == db.tables[RECODED_TABLE as int],
    ensures
        final(stores)@ == old(stores)@,
        view_rows(out@) == db.tables[RECODED_TABLE as int],
{
    let ghost table = db.tables[RECODED_TABLE as int];
    let ghost rels = crate::stores::recoded::declaration::stored_relations(db);
    proof {
        crate::stores::recoded::declaration::lemma_declared_schema();
        assert(crate::stores::recoded::declaration::stored_cols_t0() =~= seq![RECODED_COLUMN as nat]);
        lemma_proj_all_index(table, crate::stores::recoded::declaration::stored_cols_t0());
    }
    let n = rows.len();
    let lo: usize = 0;
    let coefficients = crate::stores::recoded::interface::read_coefficients(&mut stores.recoded, lo, n, Ghost(rels));
    let mut out: Vec<ERow> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == rows@.len(),
            stores@ == old(stores)@,
            view_rows(out@) == table.take(i as int),
        decreases n - i,
    {
        let mut row = clone_row(&rows[i]);
        let ghost value = table[i as int][RECODED_COLUMN as int];
        proof {
            assert(view_rows(rows@)[i as int] == view_row(rows@[i as int]@));
            assert(view_row(row@) == table[i as int]);
            assert(row_in_table(table[i as int], db.schema[RECODED_TABLE as int]));
            assert(rels[0][lo as int + i as int] == seq![Val::Num { coeff: coefficients@[i as int] as int, scale: crate::stores::recoded::interface::scale() }]);
            assert(rels[0][i as int][0] == value);
            assert(view_row(row@)[RECODED_COLUMN as int] == row@[RECODED_COLUMN as int]@);
        }
        let scale = match &row[RECODED_COLUMN] {
            EVal::Num { coeff: _, scale } => *scale,
            _ => {
                proof {
                    assert(false);
                }
                0
            },
        };
        let ghost before = row@;
        row.set(RECODED_COLUMN, EVal::Num { coeff: coefficients[i] as i128, scale });
        proof {
            assert(view_row(row@) =~= view_row(before));
        }
        out.push(row);
        proof {
            assert(view_rows(out@) =~= table.take(i as int + 1));
        }
        i += 1;
    }
    proof {
        assert(table.take(n as int) =~= table);
    }
    out
}

/// `rows` (table `ZONED_TABLE` as materialized) with column `ZONED_COLUMN` read from storage `zoned` (its kept flat
/// parts, through the plain-columns reader).
#[verifier::loop_isolation(false)]
fn replace_zoned(stores: &mut Stores, rows: Vec<ERow>, Ghost(db): Ghost<Database>) -> (out: Vec<ERow>)
    requires
        bound_db(old(stores)@, db),
        view_rows(rows@) == db.tables[ZONED_TABLE as int],
    ensures
        final(stores)@ == old(stores)@,
        view_rows(out@) == db.tables[ZONED_TABLE as int],
{
    let ghost table = db.tables[ZONED_TABLE as int];
    let ghost rels = crate::stores::zoned::declaration::stored_relations(db);
    let ghost cols = crate::stores::zoned::declaration::stored_columns_t0();
    let n = rows.len();
    if n == 0 {
        return rows;
    }
    proof {
        crate::stores::zoned::declaration::lemma_declared_schema();
    }
    let schema = schema_exec();
    proof {
        assert(view_schema(schema@)[ZONED_TABLE as int] == view_table_schema(schema@[ZONED_TABLE as int]));
    }
    let ty = schema[ZONED_TABLE].columns[ZONED_COLUMN].ty;
    proof {
        let ids = crate::stores::zoned::declaration::stored_cols_t0();
        assert(ids =~= seq![0nat, 1nat, 2nat]);
        assert forall|i: int| 0 <= i < table.len() implies #[trigger] table[i].len() == 3 by {
            assert(row_in_table(table[i], db.schema[ZONED_TABLE as int]));
        }
        assert forall|k: int| 0 <= k < 3 implies #[trigger] ids[k] == k by {
            if k == 0 {} else if k == 1 {} else {}
        }
        crate::stores::zoned::interface::plain::lemma_proj_identity(table, ids, 3);
        assert(rels[0] == table);
        assert(crate::link::source::proj_columns(schema_spec()[ZONED_TABLE as int], ids)[ZONED_COLUMN as int] == schema_spec()[ZONED_TABLE as int].columns[ZONED_COLUMN as int]);
        assert(ty == cols[ZONED_COLUMN as int].ty);
        assert(crate::stores::zoned::interface::plain::plain_column(stores@.zoned, crate::stores::zoned::interface::layout()[ZONED_COLUMN as int], cols[ZONED_COLUMN as int].ty, rels[0], ZONED_COLUMN as int));
        assert(crate::stores::zoned::interface::layout()[ZONED_COLUMN as int] == 1);
    }
    let lo: usize = 0;
    let s = read_plain(&mut stores.zoned, 1, ty, lo, n, Ghost(rels[0]), Ghost(ZONED_COLUMN as int));
    match s {
        PlainSlice::Text(offsets, bytes) => {
            let mut out: Vec<ERow> = Vec::new();
            let mut i: usize = 0;
            while i < n
                invariant
                    i <= n,
                    n == rows@.len(),
                    stores@ == old(stores)@,
                    view_rows(out@) == table.take(i as int),
                decreases n - i,
            {
                let mut row = clone_row(&rows[i]);
                let v = text_value(offsets, bytes, i);
                proof {
                    assert(view_rows(rows@)[i as int] == view_row(rows@[i as int]@));
                    assert(view_row(row@) == table[i as int]);
                    assert(row_in_table(table[i as int], db.schema[ZONED_TABLE as int]));
                    assert(rels[0][lo as int + i as int][ZONED_COLUMN as int] == plain_value(s, i as int));
                }
                let ghost before = row@;
                row.set(ZONED_COLUMN, v);
                proof {
                    assert(view_row(row@) =~= view_row(before));
                }
                out.push(row);
                proof {
                    assert(view_rows(out@) =~= table.take(i as int + 1));
                }
                i += 1;
            }
            proof {
                assert(table.take(n as int) =~= table);
            }
            out
        },
        _ => {
            proof {
                assert(false);
            }
            rows
        },
    }
}

} // verus!
