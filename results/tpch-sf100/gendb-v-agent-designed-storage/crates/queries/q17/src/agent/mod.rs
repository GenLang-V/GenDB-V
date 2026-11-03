// AUTHOR MODULE ROOT (crate::agent). You own every file under src/agent/.
//! TPC-H Q17 (small-quantity-order revenue) over the storages `li_pkqty` (lineitem of `facts` with a composite
//! (l_partkey, l_quantity) index: a dense directory over l_partkey, the stored rows in key order and each position's
//! quantity key), `custpart` (part, canonical order, p_brand / p_container as sorted dictionaries) and `part_bcs`
//! (custpart plus a (p_brand, p_container, p_size) index of the part rows).
//!
//! Plan: find `$1` and `$2` in the p_brand and p_container dictionaries (`dict_find`; a missing one keeps no row).
//! Index path (both indexes present): the part rows of a (brand, container) group of part_bcs's index are one range
//! of positions (`ixscan`), visited serially at 1 worker or as worker tasks over sub-ranges. Each matching part row
//! looks up its lineitem rows through li_pkqty's directory (`lookup::part_sum`): the quantity keys of its range (one
//! contiguous read) give the quantity sum and count, hence the exact AVG (PostgreSQL `numeric_div`), and the rows
//! with `quantity < 0.2 * AVG` add their l_extendedprice (the only random lineitem reads). Without part_bcs's index
//! the part rows are scanned in parallel ranges (`scan`). The general path (`general`, serial) covers a storage
//! without the lineitem index or a threshold outside the fast integer range, and reports `Capacity` for an AVG
//! outside the executable division domain (`sqlcap`). The answer is `SUM / 7.0` with the verified numeric division.
//!
//! Proof: `vals` states the statement over value rows, `sqlsub`/`sqlmain` prove that the SQL meaning is that value
//! model on a typed database, `bind` relates the stored parts to the database's value rows, and `answer` closes
//! the chain for every database bound to the parts.
use vstd::prelude::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok, capacity_domain};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::exec::value::*;
use crate::exec::fns::div::exec_div;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::fns::div::*;
use crate::link::query::view_rows;
use crate::link::join::sum_of;
use crate::query::{param_domain, query_spec_at};
use crate::stores::li_pkqty::interface as LI;
use crate::stores::custpart::interface::common::colfmt as CF;
use crate::stores::custpart::interface::common::read::dict_find;

pub mod common;
pub mod vals;
pub mod typed;
pub mod sqlsub;
pub mod sqlmain;
pub mod sqlcap;
pub mod bind;
pub mod lookup;
pub mod scan;
pub mod general;
pub mod answer;
pub mod read;
pub mod ixscan;

use vals::*;
use typed::*;
use sqlmain::{ptext, seven};
use bind::*;
use lookup::{LiCols, li_cols_ok};
use scan::*;
use general::*;
use answer::*;
use read::*;
use ixscan::*;

verus! {

/// The fast path: the scan of every part row, in parallel ranges when more than one worker is allowed.
fn run_fast(li: &LiCols, pa: &PaCols, tb: u64, tc: u64, workers: usize, dispatch: &mut Dispatch,
    Ghost(lp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>, Ghost(b): Ghost<Seq<u8>>, Ghost(c): Ghost<Seq<u8>>)
    -> (r: Result<Option<(i128, bool)>, QueryError>)
    requires
        li_cols_ok(*li, lp),
        pa_cols_ok(*pa, cp),
        targets_ok(lp, cp, b, c, tb, tc),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(o) ==> out_ok(lp, cp, b, c, 0, pa.n as int, o),
        r matches Err(e) ==> e is WorkerFailed,
{
    if workers == 1 {
        return Ok(scan_range(li, pa, tb, tc, 0, pa.n, Ghost(lp), Ghost(cp), Ghost(b), Ghost(c)));
    }
    let (tasks, Ghost(bnds)) = make_tasks(li, pa, tb, tc, workers, Ghost(lp), Ghost(cp), Ghost(b), Ghost(c));
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    Ok(merge(&outs, Ghost(tv), Ghost(bnds), li, pa, tb, tc, Ghost(lp), Ghost(cp), Ghost(b), Ghost(c)))
}

/// The one result row `[v]`.
fn one_row(v: EVal) -> (rows: Vec<Vec<EVal>>)
    ensures view_rows(rows@) == seq![seq![v@]],
{
    let mut row: Vec<EVal> = Vec::new();
    row.push(v);
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    rows.push(row);
    proof {
        assert(crate::exec::value::view_row(rows@[0]@) =~= seq![v@]);
        assert(view_rows(rows@) =~= seq![seq![v@]]);
    }
    rows
}

/// The answer from the totals: `SUM / 7.0` of the aggregate row.
fn finish(sum: i128, any: bool, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<Answer, QueryError>)
    requires
        param_domain(ps),
        totals_ok(sv, ps, sum as int, any),
    ensures answer_meets(sv, ps, r),
{
    let a0 = if any { EVal::Num { coeff: sum, scale: 2 } } else { EVal::Null };
    let mut args: Vec<EVal> = Vec::new();
    args.push(a0);
    args.push(EVal::Num { coeff: 70, scale: 1 });
    proof {
        assert(crate::exec::value::view_row(args@) =~= seq![aval(sum as int, any), seven()]);
        assert(crate::exec::domain::row_ts_ok(crate::exec::value::view_row(args@)));
    }
    let out = exec_div(ScalarFn::DivNumeric, &args);
    match out {
        Err(_) => {
            proof {
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
                    lemma_outcome(sv, db, ps, sum as int, any);
                }
            }
            Ok(Answer::Capacity)
        },
        Ok(Err(e)) => {
            proof {
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(e))) by {
                    lemma_outcome(sv, db, ps, sum as int, any);
                    crate::link::outcome::lemma_outcome_err(db, query_spec_at(ps), e);
                }
            }
            Ok(Answer::SqlError(e))
        },
        Ok(Ok(v)) => {
            let rows = one_row(v);
            proof {
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
                    lemma_outcome(sv, db, ps, sum as int, any);
                    crate::link::outcome::lemma_outcome_rows(db, query_spec_at(ps), seq![seq![v@]]);
                }
            }
            Ok(Answer::Rows(rows))
        },
    }
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
    let ghost ps = params@;
    let ghost lp = sv.li_pkqty;
    let ghost cp = sv.custpart;
    let ghost pp = sv.part_bcs;
    let ghost b = params.p0@;
    let ghost c = params.p1@;
    proof {
        let db0 = choose|db: Database| #[trigger] bound_db(sv, db);
        lemma_li_link(sv, db0);
        lemma_pa_link(sv, db0);
        lemma_masses(sv, db0, ps);
        lemma_pb_link(sv, db0);
        assert(ptext(ps[0]) == b && ptext(ps[1]) == c);
    }
    let (pa, d) = read_pa(&mut stores.custpart, Ghost(cp));
    let fb = dict_find(d.bo, d.by, d.bo.len() - 1, params.p0, params.p0.len());
    let fc = dict_find(d.co, d.cy, d.co.len() - 1, params.p1, params.p1.len());
    let (tb, tc) = match (fb, fc) {
        (Some(xb), Some(xc)) => (xb as u64, xc as u64),
        _ => {
            proof {
                lemma_totals_none(sv, ps);
            }
            return finish(0, false, Ghost(sv), Ghost(ps));
        },
    };
    let lb = read_li_base(&mut stores.li_pkqty, Ghost(lp));
    let fast = match read_li_dir(&mut stores.li_pkqty, &lb, Ghost(lp)) {
        Some(li) => match read_pidx(&mut stores.part_bcs, params.p0, params.p1, Ghost(pp)) {
            Some((px, bm, cm)) => {
                proof {
                    lemma_xsum_all(cp, pp, fmass(lp, b, c));
                }
                match ix_all(&li, &px, &bm, &cm, workers, dispatch, Ghost(lp), Ghost(cp), Ghost(pp), Ghost(b), Ghost(c)) {
                    Ok(o) => {
                        proof {
                            lemma_xsum_all(cp, pp, fsum(lp, b, c));
                            lemma_xsum_all(cp, pp, fcnt(lp, b, c));
                        }
                        o
                    },
                    Err(e) => return Err(e),
                }
            },
            None => match run_fast(&li, &pa, tb, tc, workers, dispatch, Ghost(lp), Ghost(cp), Ghost(b), Ghost(c)) {
                Ok(o) => {
                    proof {
                        assert(zrows(cp).subrange(0, pa.n as int) =~= zrows(cp));
                    }
                    o
                },
                Err(e) => return Err(e),
            },
        },
        None => None,
    };
    match fast {
        Some((sum, any)) => {
            proof {
                lemma_totals_fast(sv, ps, sum as int, any);
            }
            finish(sum, any, Ghost(sv), Ghost(ps))
        },
        None => match general_all(&lb, &pa, tb, tc, Ghost(lp), Ghost(cp), Ghost(b), Ghost(c)) {
            Ok((sum, any)) => {
                proof {
                    lemma_totals_gen(sv, ps, sum as int, any);
                }
                finish(sum, any, Ghost(sv), Ghost(ps))
            },
            Err(j) => {
                proof {
                    assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
                        lemma_li_link(sv, db);
                        lemma_pa_link(sv, db);
                        let k = pkey_at(cp, j as int);
                        lemma_perm_sub(srows(lp), ys_of(db), k);
                        assert(zs_of(db)[j as int] == zrow(cp, j as int));
                        crate::link::source::lemma_proj_all_index(db.tables[3], pcols());
                        assert(zs_of(db)[j as int][0] == db.tables[3][j as int][0]);
                        crate::agent::sqlcap::lemma_cap(db, ps, j as int);
                    }
                }
                Ok(Answer::Capacity)
            },
        },
    }
}

} // verus!
