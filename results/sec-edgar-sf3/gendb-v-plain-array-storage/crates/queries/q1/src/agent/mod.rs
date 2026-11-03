//! SELECT stmt, rfile, COUNT(*), COUNT(DISTINCT adsh), AVG(line) FROM pre WHERE stmt IS NOT NULL
//! GROUP BY stmt, rfile ORDER BY COUNT(*) DESC, over the flat storages of `pre` and `sub`.
//!
//! Plan: the adsh values of `sub` (primary key) form a dictionary (`dict`); the rows of `pre` are split into
//! cost-balanced ranges, one worker task each (`kernel`: groups by (stmt, rfile), counts, line sums and, per `sub`
//! row, the bit set of groups having that adsh); the ranges' groups are merged (`merge`) and the distinct adsh
//! counts are counted over id ranges by a second set of tasks (`distinct`). When that path cannot run (more than 16
//! groups in a range or 64 in all, or an adsh the dictionary does not find) a serial path computes the same
//! (`serial`). The rows are sorted by COUNT(*) descending (`out`). The proof relates the groups to the SQL meaning
//! (`sql`, `out`, `errs`) for every database bound to the parts (`bind`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::order::*;
use crate::gendb_entry::*;
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec, query_spec_at};
use crate::exec::value::*;
use crate::exec::ast::EOrderKey;
use crate::exec::relational::order::{sort_rows_exec, view_keys};
use crate::link::query::{gkeys, view_rows};
use crate::exec::relational::domain::fits_query;
use crate::agent::cols::*;
use crate::agent::spec::*;
use crate::agent::kernel::gkey;
use crate::agent::merge::Groups;
use crate::agent::serial::{final_ok, serial_groups};
use crate::agent::run::fast_groups;
use crate::agent::sql::{gq, full_row};
use crate::agent::out::*;
use crate::agent::errs::*;
use crate::agent::bind::*;
use crate::agent::distinct::sub_distinct;

pub mod common;
pub mod spec;
pub mod cols;
pub mod dict;
pub mod kernel;
pub mod merge;
pub mod distinct;
pub mod serial;
pub mod run;
pub mod sql;
pub mod out;
pub mod errs;
pub mod bind;

verus! {

/// The answer for groups `gs` of the table `t` (every count inside int8 checked first).
fn answer(c: &Cols, Ghost(t): Ghost<Seq<Row>>, gs: &Groups) -> (r: Answer)
    requires cols_wf(*c), corr(*c, t), final_ok(t, c.n as int, c.n as int, *gs),
    ensures
        forall|db: Database| 3 < db.tables.len() && db.tables[3] == t ==> outcome_ok(db, query_spec(), Ok::<Answer, QueryError>(r)),
{
    let mut g: usize = 0;
    while g < gs.rep.len()
        invariant
            cols_wf(*c), corr(*c, t), final_ok(t, c.n as int, c.n as int, *gs), g <= gs.rep@.len(),
            forall|g2: int| 0 <= g2 < g ==> #[trigger] gs.cnt@[g2] <= crate::spec::limits::int8_max(),
        decreases gs.rep@.len() - g,
    {
        if gs.cnt[g] > 0x7fff_ffff_ffff_ffffu64 {
            proof {
                let k = gkey(t, gs.rep@, g as int);
                lemma_same_groups(*c, t, *gs);
                assert(gkeys(gq(), t).contains(k));
                assert forall|db: Database| 3 < db.tables.len() && db.tables[3] == t
                    implies outcome_ok(db, query_spec(), Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))) by {
                    lemma_count_error(*c, db, t, k);
                }
            }
            return Answer::SqlError(SqlError::NumericValueOutOfRange);
        }
        g = g + 1;
    }
    let rows = match build_rows(c, Ghost(t), gs) {
        Ok(r) => r,
        Err(bad) => {
            proof {
                let k = gkey(t, gs.rep@, bad as int);
                lemma_same_groups(*c, t, *gs);
                assert(gkeys(gq(), t).contains(k));
                assert forall|k2: Row| #[trigger] gkeys(gq(), t).contains(k2) implies cnt_r(t, k2, 0, t.len() as int) <= crate::spec::limits::int8_max() by {
                    let g2 = choose|g2: int| 0 <= g2 < gs.rep@.len() && gkey(t, gs.rep@, g2) == k2;
                    assert(gs.cnt@[g2] <= crate::spec::limits::int8_max());
                }
                assert forall|db: Database| 3 < db.tables.len() && db.tables[3] == t
                    implies outcome_ok(db, query_spec(), Ok::<Answer, QueryError>(Answer::Capacity)) by {
                    lemma_avg_capacity(*c, db, t, k);
                }
            }
            return Answer::Capacity;
        },
    };
    let mut keys: Vec<EOrderKey> = Vec::new();
    keys.push(EOrderKey { col: 2, desc: true, nulls_first: true });
    let ghost rv = crate::exec::relational::schema::view_rows(rows@);
    let sorted = sort_rows_exec(&keys, rows);
    proof {
        assert(view_keys(keys@) =~= okeys());
        assert(view_rows(sorted@) =~= crate::exec::relational::schema::view_rows(sorted@));
        assert forall|g2: int| 0 <= g2 < rv.len() implies #[trigger] rv[g2] == full_row(t, gkey(t, gs.rep@, g2))
            && crate::agent::sql::group_fits(t, gkey(t, gs.rep@, g2)) by {
            assert(rv[g2] == view_row(rows@[g2]@));
        }
        assert forall|db: Database| 3 < db.tables.len() && db.tables[3] == t
            implies outcome_ok(db, query_spec(), Ok::<Answer, QueryError>(Answer::Rows(sorted))) by {
            lemma_rows_ok(*c, db, t, *gs, rv);
        }
    }
    Answer::Rows(sorted)
}

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    proof {
        assert(bound_db(sv, db0));
        assert(crate::stores::flat_pre::interface::represents(sv.flat_pre, crate::stores::flat_pre::declaration::stored_relations(db0)));
        assert(crate::stores::flat_sub::interface::represents(sv.flat_sub, crate::stores::flat_sub::declaration::stored_relations(db0)));
    }
    let c = load_cols(stores);
    let ghost t = pre_rows(sv.flat_pre);
    proof { lemma_sub_distinct(c, sv, db0); }
    let gs = match fast_groups(&c, Ghost(t), workers, dispatch) {
        Ok(Some(g)) => g,
        Ok(None) => serial_groups(&c, Ghost(t)),
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let a = answer(&c, Ghost(t), &gs);
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(params@), Ok::<Answer, QueryError>(a)) by {
            lemma_pre_table(sv, db);
        }
    }
    Ok(a)
}

} // verus!
